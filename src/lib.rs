// #![warn(missing_docs)]

/*!
Lenient parser or Semantic Version ranges.
*/

use lenient_semver_parser::{parse_partial, ErrorKind, VersionBuilder};
use lenient_version::Version;

pub fn parse<'a>(input: &'a str) -> Result<RangeSet<'a>, Box<dyn std::error::Error + 'a>> {
    parse_compat(input, Compat::Npm)
}

pub fn parse_cargp<'a>(input: &'a str) -> Result<RangeSet<'a>, Box<dyn std::error::Error + 'a>> {
    parse_compat(input, Compat::Cargo)
}

pub fn parse_npm<'a>(input: &'a str) -> Result<RangeSet<'a>, Box<dyn std::error::Error + 'a>> {
    parse_compat(input, Compat::Npm)
}

pub fn parse_compat<'input>(
    mut input: &'input str,
    compat: Compat,
) -> Result<RangeSet<'input>, Box<dyn std::error::Error + 'input>> {
    let mut ranges = vec![];
    let mut operations: Vec<Operation> = vec![];
    let mut allow_chain_operators = false;
    loop {
        let (op, next_input) = match input.as_bytes() {
            &[] => {
                if !operations.is_empty() {
                    ranges.push(operations);
                }
                break;
            }
            &[b'|', b'|', ..] if allow_chain_operators => {
                let operations = std::mem::take(&mut operations);
                ranges.push(operations);
                input = &input[2..];
                allow_chain_operators = false;
                continue;
            }
            &[b',', ..] if allow_chain_operators => {
                input = &input[1..];
                allow_chain_operators = false;
                continue;
            }
            &[b' ', ..] => {
                input = &input[1..];
                continue;
            }
            &[b'-', ..] => (Op::Hyphen, &input[1..]),
            &[b'^', ..] => (Op::Caret, &input[1..]),
            &[b'~', ..] => (Op::Tilde, &input[1..]),
            &[b'>', b'=', ..] => (Op::Gte, &input[2..]),
            &[b'>', ..] => (Op::Gt, &input[1..]),
            &[b'<', b'=', ..] => (Op::Lte, &input[2..]),
            &[b'<', ..] => (Op::Lt, &input[1..]),
            &[b'=', ..] => (Op::Eq, &input[1..]),
            _ => (Op::Nothing, input),
        };

        let (version, remainder) = parse_next_version(next_input)?;
        let op = match op {
            Op::Nothing => Operation::Default(version),
            Op::Eq => Operation::Apply(Operator::Eq, version),
            Op::Gt => Operation::Apply(Operator::Gt, version),
            Op::Gte => Operation::Apply(Operator::Gte, version),
            Op::Lt => Operation::Apply(Operator::Lt, version),
            Op::Lte => Operation::Apply(Operator::Lte, version),
            Op::Tilde => Operation::Tilde(version),
            Op::Caret => Operation::Caret(version),
            Op::Hyphen => {
                let prev = operations
                    .pop()
                    .ok_or_else(|| String::from("The hyphen operator requires a previous range"))?;

                let prev = match prev {
                    Operation::Default(prev) => prev,
                    otherwise => {
                        Err(format!(
                            "The hyphen operator does not allow the previous range to use an operator, but the previous entry is {:?}",
                            otherwise
                        ))?;
                        unreachable!()
                    }
                };

                Operation::Hyphen(prev, version)
            }
        };
        operations.push(op);

        allow_chain_operators = true;
        input = remainder;
    }

    let ranges = ranges
        .into_iter()
        .map(|ops| {
            let mut comparators = Vec::with_capacity(ops.len());
            for op in ops {
                let (first, second) = op.into_versions(compat);
                comparators.push(first);
                if let Some(comparator) = second {
                    comparators.push(comparator);
                }
            }

            Range { comparators }
        })
        .collect();

    Ok(RangeSet { ranges })
}

#[inline]
fn parse_next_version<'input>(
    input: &'input str,
) -> Result<(VersionQualifier<'input>, &'input str), lenient_semver_parser::Error<'input>> {
    match parse_partial::<VersionQualifier<'input>>(input) {
        Ok(v) => Ok(v),
        Err(err) => {
            if err.error_kind() == ErrorKind::UnexpectedInput {
                if matches!(err.erroneous_input(), "x" | "X" | "*" | "?") {
                    let span = err.error_span();
                    return Ok((VersionQualifier::empty(), &input[span.end..]));
                }
            }
            Err(err)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RangeSet<'input> {
    ranges: Vec<Range<'input>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Compat {
    /// default  operator is ^
    Cargo,
    /// default opertaor is =
    Npm,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Range<'input> {
    comparators: Vec<Comparator<'input>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Comparator<'input> {
    op: Operator,
    version: Version<'input>,
}

impl<'input> Comparator<'input> {
    fn gte(version: Version<'input>) -> Self {
        Self {
            op: Operator::Gte,
            version,
        }
    }

    fn lt(version: Version<'input>) -> Self {
        Self {
            op: Operator::Lt,
            version,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Operator {
    /// Equal, =
    Eq,
    /// Greater than, >
    Gt,
    /// Greater than or equal, >=
    Gte,
    /// Less than, <
    Lt,
    /// Less than or equal, <=
    Lte,
}

impl Operator {
    fn or_if_eq(self, other: Self) -> Self {
        if self == Self::Eq {
            other
        } else {
            self
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Op {
    Nothing,
    Eq,
    Gt,
    Gte,
    Lt,
    Lte,
    Tilde,
    Caret,
    Hyphen,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Operation<'input> {
    Default(VersionQualifier<'input>),
    Apply(Operator, VersionQualifier<'input>),
    Tilde(VersionQualifier<'input>),
    Caret(VersionQualifier<'input>),
    Hyphen(VersionQualifier<'input>, VersionQualifier<'input>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum VersionNumber {
    Unspecified,
    Wildcard,
    Num(u64),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Segment {
    Empty,
    Major,
    Minor,
    Patch,
    Additional,
    PreRelease,
}

impl From<VersionNumber> for u64 {
    fn from(v: VersionNumber) -> Self {
        match v {
            VersionNumber::Unspecified => 0,
            VersionNumber::Wildcard => 0,
            VersionNumber::Num(n) => n,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct VersionQualifier<'input> {
    segment: Segment,
    major: VersionNumber,
    minor: VersionNumber,
    patch: VersionNumber,
    additional: Vec<VersionNumber>,
    pre: Vec<&'input str>,
    build: Vec<&'input str>,
}

impl<'input> VersionQualifier<'input> {
    const fn empty() -> Self {
        Self {
            segment: Segment::Empty,
            major: VersionNumber::Unspecified,
            minor: VersionNumber::Unspecified,
            patch: VersionNumber::Unspecified,
            additional: Vec::new(),
            pre: Vec::new(),
            build: Vec::new(),
        }
    }

    fn to_version<F>(self, mut f: F) -> Version<'input>
    where
        F: for<'a> FnMut(&'a mut Version<'input>),
    {
        let mut version = Version {
            major: self.major.into(),
            minor: self.minor.into(),
            patch: self.patch.into(),
            additional: self.additional.into_iter().map(u64::from).collect(),
            pre: self.pre,
            build: self.build,
        };
        f(&mut version);
        version
    }
}

impl<'input> VersionBuilder<'input> for VersionQualifier<'input> {
    type Out = Self;

    fn new() -> Self {
        Self::empty()
    }

    fn set_major(&mut self, major: u64) {
        self.major = VersionNumber::Num(major);
        self.segment = Segment::Major;
    }

    fn set_minor(&mut self, minor: u64) {
        self.minor = VersionNumber::Num(minor);
        self.segment = Segment::Minor;
    }

    fn set_patch(&mut self, patch: u64) {
        self.patch = VersionNumber::Num(patch);
        self.segment = Segment::Patch;
    }

    fn add_additional(&mut self, num: u64) {
        self.additional.push(VersionNumber::Num(num));
        self.segment = Segment::Additional;
    }

    fn add_pre_release(&mut self, pre_release: &'input str) {
        if matches!(pre_release, "x" | "X" | "*" | "?") {
            if self.major == VersionNumber::Unspecified {
                self.major = VersionNumber::Wildcard;
            } else if self.minor == VersionNumber::Unspecified {
                self.minor = VersionNumber::Wildcard;
            } else if self.patch == VersionNumber::Unspecified {
                self.patch = VersionNumber::Wildcard;
            } else if self.segment == Segment::PreRelease {
                self.pre.push(pre_release);
            } else {
                self.additional.push(VersionNumber::Wildcard);
            }
        } else {
            self.pre.push(pre_release);
            self.segment = Segment::PreRelease;
        }
    }

    fn add_build(&mut self, build: &'input str) {
        self.build.push(build)
    }

    fn build(self) -> Self::Out {
        self
    }
}

impl<'input> Operation<'input> {
    fn into_versions(self, compat: Compat) -> (Comparator<'input>, Option<Comparator<'input>>) {
        match self {
            Operation::Default(v) => match compat {
                Compat::Cargo => Operation::Caret(v).into_versions(compat),
                Compat::Npm => Operation::Apply(Operator::Eq, v).into_versions(compat),
            },
            Operation::Apply(op, v) => match v.major {
                VersionNumber::Wildcard | VersionNumber::Unspecified => (
                    Comparator {
                        op: op.or_if_eq(Operator::Gte),
                        version: v.to_version(|v| v.set_major(0)),
                    },
                    None,
                ),
                VersionNumber::Num(major) => match v.minor {
                    VersionNumber::Unspecified | VersionNumber::Wildcard => {
                        let min = Comparator {
                            op: op.or_if_eq(Operator::Gte),
                            version: v.to_version(|v| v.set_minor(0)),
                        };

                        let max = major
                            .checked_add(1)
                            .map(|m| Comparator::lt(Version::new(m, 0, 0)));

                        (min, max)
                    }
                    VersionNumber::Num(minor) => match v.patch {
                        VersionNumber::Unspecified | VersionNumber::Wildcard => {
                            let min = Comparator {
                                op: op.or_if_eq(Operator::Gte),
                                version: v.to_version(|v| v.set_patch(0)),
                            };

                            let max = minor
                                .checked_add(1)
                                .map(|m| Comparator::lt(Version::new(major, m, 0)));

                            (min, max)
                        }
                        VersionNumber::Num(_) => (
                            Comparator {
                                op,
                                version: v.to_version(|_| ()),
                            },
                            None,
                        ),
                    },
                },
            },
            Operation::Tilde(v) => match v.segment {
                Segment::Empty => (Comparator::gte(Version::new(0, 0, 0)), None),
                Segment::Major => {
                    let major = u64::from(v.major);
                    (
                        Comparator::gte(Version::new(major, 0, 0)),
                        major
                            .checked_add(1)
                            .map(|m| Comparator::lt(Version::new(m, 0, 0))),
                    )
                }
                Segment::Minor | Segment::Patch | Segment::Additional => {
                    let major = u64::from(v.major);
                    let minor = u64::from(v.minor);
                    let version = v.to_version(|_| ());
                    (
                        Comparator::gte(version),
                        minor
                            .checked_add(1)
                            .map(|m| Comparator::lt(Version::new(major, m, 0))),
                    )
                }
                Segment::PreRelease => {
                    let min = Version {
                        major: u64::from(v.major),
                        minor: u64::from(v.minor),
                        patch: u64::from(v.patch),
                        additional: v.additional.into_iter().map(u64::from).collect(),
                        pre: v.pre,
                        build: v.build,
                    };
                    let max = min.clone();
                    (Comparator::gte(min), Some(Comparator::lt(max)))
                }
            },
            Operation::Caret(v) => {
                let major = u64::from(v.major);
                let minor = u64::from(v.minor);
                let patch = u64::from(v.patch);

                if major > 0 {
                    (
                        Comparator::gte(Version::new(major, minor, patch)),
                        major
                            .checked_add(1)
                            .map(|m| Comparator::lt(Version::new(m, 0, 0))),
                    )
                } else if minor > 0 {
                    (
                        Comparator::gte(Version::new(0, minor, patch)),
                        minor
                            .checked_add(1)
                            .map(|m| Comparator::lt(Version::new(0, m, 0))),
                    )
                } else if patch > 0 {
                    (
                        Comparator::gte(Version::new(0, 0, patch)),
                        patch
                            .checked_add(1)
                            .map(|m| Comparator::lt(Version::new(0, 0, m))),
                    )
                } else {
                    match v.segment {
                        Segment::Major => (
                            Comparator::gte(Version::empty()),
                            Some(Comparator::lt(Version::new(1, 0, 0))),
                        ),
                        Segment::Minor => (
                            Comparator::gte(Version::empty()),
                            Some(Comparator::lt(Version::new(0, 1, 0))),
                        ),
                        Segment::Patch => (
                            Comparator::gte(Version::empty()),
                            Some(Comparator::lt(Version::new(0, 0, 1))),
                        ),
                        Segment::Empty => {
                            todo!()
                        }
                        Segment::Additional => {
                            todo!()
                        }
                        Segment::PreRelease => {
                            todo!()
                        }
                    }
                }
            }
            Operation::Hyphen(prev, next) => {
                let (prev, _) = Operation::Apply(Operator::Gte, prev).into_versions(compat);
                let next = match next.segment {
                    Segment::Empty => None,
                    Segment::Major => {
                        let major = u64::from(next.major);
                        major
                            .checked_add(1)
                            .map(|m| Comparator::lt(Version::new(m, 0, 0)))
                    }
                    Segment::Minor => {
                        let major = u64::from(next.major);
                        let minor = u64::from(next.minor);
                        minor
                            .checked_add(1)
                            .map(|m| Comparator::lt(Version::new(major, m, 0)))
                    }
                    _ => Some(
                        Operation::Apply(Operator::Lte, next)
                            .into_versions(compat)
                            .0,
                    ),
                };
                (prev, next)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hyphen_1() {
        assert_eq!(
            parse("1.2.3 - 2.3.4").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 3)
                        },
                        Comparator {
                            op: Operator::Lte,
                            version: Version::new(2, 3, 4)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_hyphen_2() {
        assert_eq!(
            parse("1.2 - 2.3.4").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 0)
                        },
                        Comparator {
                            op: Operator::Lte,
                            version: Version::new(2, 3, 4)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_hyphen_3() {
        assert_eq!(
            parse("1.2.3 - 2.3").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 3)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(2, 4, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_hyphen_4() {
        assert_eq!(
            parse("1.2.3 - 2").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 3)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(3, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_x_1() {
        assert_eq!(
            parse("*").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![Comparator {
                        op: Operator::Gte,
                        version: Version::new(0, 0, 0)
                    },]
                }]
            }
        );
    }

    #[test]
    fn test_x_2() {
        assert_eq!(
            parse("1.x").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 0, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(2, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_x_3() {
        assert_eq!(
            parse("1.2.x").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(1, 3, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_x_4() {
        assert_eq!(parse("").unwrap(), RangeSet { ranges: vec![] });
    }

    #[test]
    fn test_x_5() {
        assert_eq!(
            parse("1.x.x").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 0, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(2, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_tilde_1() {
        assert_eq!(
            parse("~1.2.3").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 3)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(1, 3, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_tilde_2() {
        assert_eq!(
            parse("~1.2").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(1, 3, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_tilde_3() {
        assert_eq!(
            parse("~1").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 0, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(2, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_tilde_4() {
        assert_eq!(
            parse("~0.2.3").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(0, 2, 3)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(0, 3, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_tilde_5() {
        assert_eq!(
            parse("~0.2").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(0, 2, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(0, 3, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_tilde_6() {
        assert_eq!(
            parse("~0").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(0, 0, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(1, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_caret_1() {
        assert_eq!(
            parse("^1.2.3").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 3)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(2, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_caret_2() {
        assert_eq!(
            parse("^0.2.3").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(0, 2, 3)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(0, 3, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_caret_3() {
        assert_eq!(
            parse("^0.0.3").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(0, 0, 3)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(0, 0, 4)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_caret_4() {
        assert_eq!(
            parse("^1.2.x").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 2, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(2, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_caret_5() {
        assert_eq!(
            parse("^0.0.x").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(0, 0, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(0, 1, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_caret_6() {
        assert_eq!(
            parse("^0.0").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(0, 0, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(0, 1, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_caret_7() {
        assert_eq!(
            parse("^1.x").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(1, 0, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(2, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_caret_8() {
        assert_eq!(
            parse("^0.x").unwrap(),
            RangeSet {
                ranges: vec![Range {
                    comparators: vec![
                        Comparator {
                            op: Operator::Gte,
                            version: Version::new(0, 0, 0)
                        },
                        Comparator {
                            op: Operator::Lt,
                            version: Version::new(1, 0, 0)
                        },
                    ]
                }]
            }
        );
    }

    #[test]
    fn test_or_1() {
        assert_eq!(
            parse("1.2.7 || >=1.2.9 <2.0.0").unwrap(),
            RangeSet {
                ranges: vec![
                    Range {
                        comparators: vec![Comparator {
                            op: Operator::Eq,
                            version: Version::new(1, 2, 7)
                        },]
                    },
                    Range {
                        comparators: vec![
                            Comparator {
                                op: Operator::Gte,
                                version: Version::new(1, 2, 9)
                            },
                            Comparator {
                                op: Operator::Lt,
                                version: Version::new(2, 0, 0)
                            },
                        ]
                    },
                ]
            }
        );
    }
}
