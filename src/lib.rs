// #![warn(missing_docs)]

/*!
Lenient parser or Semantic Version ranges.
*/

use lenient_semver_parser::{parse_partial, VersionBuilder};
use lenient_version::Version;

pub fn parse<'a>(input: &'a str) -> Result<RangeSet<'a>, Box<dyn std::error::Error + 'a>> {
    parse_compat(input, Compat::Cargo)
}

pub fn parse_npm<'a>(input: &'a str) -> Result<RangeSet<'a>, Box<dyn std::error::Error + 'a>> {
    parse_compat(input, Compat::Npm)
}

pub fn parse_compat<'a>(
    mut input: &'a str,
    compat: Compat,
) -> Result<RangeSet<'a>, Box<dyn std::error::Error + 'a>> {
    let default_op = match compat {
        Compat::Cargo => Op::Caret,
        Compat::Npm => Op::Eq,
    };
    let mut ranges = vec![];
    let mut comparators = vec![];
    let mut allow_chain_operators = true;
    loop {
        let (op, next_input) = match input.as_bytes() {
            &[] => {
                if !comparators.is_empty() {
                    ranges.push(Range { comparators });
                }
                return Ok(RangeSet { ranges });
            }
            &[b'|', b'|', ..] if allow_chain_operators => {
                let comparators = std::mem::take(&mut comparators);
                ranges.push(Range { comparators });
                input = &input[2..];
                allow_chain_operators = false;
                continue;
            }
            &[b',', ..] if allow_chain_operators => {
                input = &input[1..];
                allow_chain_operators = false;
                continue;
            }
            &[b' ', ..] if allow_chain_operators => {
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
            _ => (default_op, input),
        };

        let (version, remainder) = parse_partial::<VersionQualifier<'a>>(next_input)?;

        let prev = if op == Op::Hyphen {
            let prev = comparators
                .pop()
                .ok_or_else(|| String::from("The hyphen operator requires a previous range"))?;

            if prev.op != Operator::Eq {
                Err(format!(
                    "The hyphen operator does not allow the previous range to use an operator, but the version [{}] is using the operator [{:?}]",
                    prev.version, prev.op
                ))?;
            }

            Some(prev.version)
        } else {
            None
        };

        let ((op, version), other) = version.into_versions(op, prev);
        comparators.push(Comparator { op, version });
        if let Some((op, version)) = other {
            comparators.push(Comparator { op, version });
        }

        input = remainder;
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RangeSet<'input> {
    ranges: Vec<Range<'input>>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Compat {
    /// default  operator is ^
    Cargo,
    /// default opertaor is =
    Npm,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Range<'input> {
    comparators: Vec<Comparator<'input>>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Comparator<'input> {
    op: Operator,
    version: Version<'input>,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum Op {
    Eq,
    Gt,
    Gte,
    Lt,
    Lte,
    Tilde,
    Caret,
    Hyphen,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum VersionNumber {
    Unspecified,
    Wildcard,
    Num(u64),
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<'input> VersionQualifier<'input> {
    fn into_versions(
        self,
        op: Op,
        prev: Option<Version<'input>>,
    ) -> (
        (Operator, Version<'input>),
        Option<(Operator, Version<'input>)>,
    ) {
        match op {
            Op::Eq | Op::Gt | Op::Gte | Op::Lt | Op::Lte => (
                (
                    match op {
                        Op::Eq => Operator::Eq,
                        Op::Gt => Operator::Gt,
                        Op::Gte => Operator::Gte,
                        Op::Lt => Operator::Lt,
                        Op::Lte => Operator::Lte,
                        Op::Tilde => unreachable!(),
                        Op::Caret => unreachable!(),
                        Op::Hyphen => unreachable!(),
                    },
                    Version {
                        major: self.major.into(),
                        minor: self.minor.into(),
                        patch: self.patch.into(),
                        additional: self.additional.into_iter().map(u64::from).collect(),
                        pre: self.pre,
                        build: self.build,
                    },
                ),
                None,
            ),
            Op::Tilde => match self.segment {
                Segment::Empty => ((Operator::Gte, Version::new(0, 0, 0)), None),
                Segment::Major => {
                    let major = u64::from(self.major);
                    (
                        (Operator::Gte, Version::new(major, 0, 0)),
                        major
                            .checked_add(1)
                            .map(|m| (Operator::Lt, Version::new(m, 0, 0))),
                    )
                }
                Segment::Minor => {
                    let major = u64::from(self.major);
                    let minor = u64::from(self.minor);
                    (
                        (Operator::Gte, Version::new(major, minor, 0)),
                        minor
                            .checked_add(1)
                            .map(|m| (Operator::Lt, Version::new(major, m, 0))),
                    )
                }
                Segment::Patch => {
                    let major = u64::from(self.major);
                    let minor = u64::from(self.minor);
                    let patch = u64::from(self.patch);
                    (
                        (Operator::Gte, Version::new(major, minor, patch)),
                        minor
                            .checked_add(1)
                            .map(|m| (Operator::Lt, Version::new(major, minor, m))),
                    )
                }
                Segment::Additional => {
                    let major = u64::from(self.major);
                    let minor = u64::from(self.minor);
                    let patch = u64::from(self.patch);

                    let mut min = Version::new(major, minor, patch);
                    min.additional = self.additional.into_iter().map(u64::from).collect();

                    let max = min
                        .additional
                        .last()
                        .expect("empty additional")
                        .checked_add(1)
                        .map(|m| {
                            let mut add = min.additional.clone();
                            *add.last_mut().expect("empty additional") = m;
                            let mut max = Version::new(major, minor, patch);
                            max.additional = add;
                            (Operator::Lt, max)
                        });

                    ((Operator::Gte, min), max)
                }
                Segment::PreRelease => {
                    let min = Version {
                        major: u64::from(self.major),
                        minor: u64::from(self.minor),
                        patch: u64::from(self.patch),
                        additional: self.additional.into_iter().map(u64::from).collect(),
                        pre: self.pre,
                        build: self.build,
                    };
                    let max = min.clone();
                    ((Operator::Gte, min), Some((Operator::Lt, max)))
                }
            },
            Op::Caret => {
                let major = u64::from(self.major);
                let minor = u64::from(self.minor);
                let patch = u64::from(self.patch);

                if major > 0 {
                    (
                        (Operator::Gte, Version::new(major, minor, patch)),
                        major
                            .checked_add(1)
                            .map(|m| (Operator::Lt, Version::new(m, 0, 0))),
                    )
                } else if minor > 0 {
                    (
                        (Operator::Gte, Version::new(0, minor, patch)),
                        minor
                            .checked_add(1)
                            .map(|m| (Operator::Lt, Version::new(0, m, 0))),
                    )
                } else if patch > 0 {
                    (
                        (Operator::Gte, Version::new(0, 0, patch)),
                        patch
                            .checked_add(1)
                            .map(|m| (Operator::Lt, Version::new(0, 0, m))),
                    )
                } else {
                    match self.segment {
                        Segment::Major => (
                            (Operator::Gte, Version::empty()),
                            Some((Operator::Lt, Version::new(1, 0, 0))),
                        ),
                        Segment::Minor => (
                            (Operator::Gte, Version::empty()),
                            Some((Operator::Lt, Version::new(0, 1, 0))),
                        ),
                        Segment::Patch => (
                            (Operator::Gte, Version::empty()),
                            Some((Operator::Lt, Version::new(0, 0, 1))),
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
            Op::Hyphen => {
                let prev = (Operator::Gte, prev.expect("previous version"));
                let next = match self.segment {
                    Segment::Empty => None,
                    Segment::Major => {
                        let major = u64::from(self.major);
                        major
                            .checked_add(1)
                            .map(|m| (Operator::Lt, Version::new(m, 0, 0)))
                    }
                    Segment::Minor => {
                        let major = u64::from(self.major);
                        let minor = u64::from(self.minor);
                        minor
                            .checked_add(1)
                            .map(|m| (Operator::Lt, Version::new(major, m, 0)))
                    }
                    _ => Some(self.into_versions(Op::Lte, None).0),
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
        assert_eq!(
            parse("").unwrap(),
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
