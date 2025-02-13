use std::convert::TryInto;

use crate::analysis::parsing::{statement::{self, CompoundContent, SwitchCase},
                               structure::ObjectStatementsContent,
                               types::{LayoutContent, StructTypeContent}};
use crate::span::{Range, ZeroIndexed, Row, Column};
use crate::analysis::LocalDMLError;
use crate::analysis::parsing::tree::{ZeroRange, Content, TreeElement};
use serde::{Deserialize, Serialize};
use super::Rule;

pub const MAX_LENGTH_DEFAULT: u32 = 80;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct LongLineOptions {
    pub max_length: u32,
}

pub struct LongLinesRule {
    pub enabled: bool,
    pub max_length: u32,
}

impl LongLinesRule {
    pub fn from_options(options: &Option<LongLineOptions>) -> LongLinesRule {
        match options {
            Some(long_lines) => LongLinesRule {
                enabled: true,
                max_length: long_lines.max_length,
            },
            None => LongLinesRule {
                enabled: false,
                max_length: MAX_LENGTH_DEFAULT,
            },
        }
    }
    pub fn check(&self, acc: &mut Vec<LocalDMLError>, row: usize, line: &str) {
        if !self.enabled { return; }
        let len = line.len().try_into().unwrap();
        if len > self.max_length {
            let rowu32 = row.try_into().unwrap();
            let msg = LongLinesRule::description().to_owned()
                + format!(" of {} characters", self.max_length).as_str();
            let dmlerror = LocalDMLError {
                range: Range::<ZeroIndexed>::from_u32(rowu32, rowu32, self.max_length, len),
                description: msg,
            };
            acc.push(dmlerror);
        }
    }
}
impl Rule for LongLinesRule {
    fn name() -> &'static str {
        "LONG_LINE"
    }
    fn description() -> &'static str {
        "Line length is above the threshold"
    }
}

pub struct IN3Rule {
    pub enabled: bool,
    indentation_spaces: u32
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct IN3Options {
    pub indentation_spaces: u32,
}
pub struct IN3Args<'a> {
    members_ranges: Vec<ZeroRange>,
    lbrace: ZeroRange,
    rbrace: ZeroRange,
    expected_depth: &'a mut u32,
}

impl IN3Args<'_> {
    pub fn from_obj_stmts_content<'a>(node: &ObjectStatementsContent, depth: &'a mut u32) -> Option<IN3Args<'a>> {
        if let ObjectStatementsContent::List(lbrace, stmnts, rbrace) = node {
            Some(IN3Args {
                members_ranges: stmnts.iter().map(|s| s.range()).collect(),
                lbrace: lbrace.range(),
                rbrace: rbrace.range(),
                expected_depth: depth,
            })
        } else {
            None
        }
    }
    pub fn from_struct_type_content<'a>(node: &StructTypeContent, depth: &'a mut u32) -> Option<IN3Args<'a>> {
        Some(IN3Args {
            members_ranges: node.members.iter().map(|m| m.range()).collect(),
            lbrace: node.lbrace.range(),
            rbrace: node.rbrace.range(),
            expected_depth: depth,
        })
    }
    pub fn from_compound_content<'a>(node: &CompoundContent, depth: &'a mut u32) -> Option<IN3Args<'a>> {
        Some(IN3Args {
            members_ranges: node.statements.iter().map(|s| s.range()).collect(),
            lbrace: node.lbrace.range(),
            rbrace: node.rbrace.range(),
            expected_depth: depth,
        })
    }
    pub fn from_layout_content<'a>(node: &LayoutContent, depth: &'a mut u32) -> Option<IN3Args<'a>> {
        Some(IN3Args {
            members_ranges: node.fields.iter().map(|m| m.range()).collect(),
            lbrace: node.lbrace.range(),
            rbrace: node.rbrace.range(),
            expected_depth: depth,
        })
    }
}

impl IN3Rule {
    pub fn from_options(options: &Option<IN3Options>) -> IN3Rule {
        match options {
            Some(options) => IN3Rule {
                enabled: true,
                indentation_spaces: options.indentation_spaces
            },
            None => IN3Rule {
                enabled: false,
                indentation_spaces: 0
            }
        }
    }
    pub fn check<'a>(&self, acc: &mut Vec<LocalDMLError>,
        args: Option<IN3Args<'a>>)
    {
        if !self.enabled { return; }
        let Some(args) = args else { return; };
        if args.lbrace.row_start == args.rbrace.row_start ||
            args.lbrace.row_start == args.members_ranges[0].row_start { return; }
        *args.expected_depth += 1;
        for member_range in args.members_ranges {
            if self.indentation_is_not_aligned(member_range, *args.expected_depth) {
                let dmlerror = LocalDMLError {
                    range: member_range,
                    description: Self::description().to_string(),
                };
                acc.push(dmlerror);
            }
        }
    }
    fn indentation_is_not_aligned(&self, member_range: ZeroRange, depth: u32) -> bool {
        // Implicit IN1
        let expected_column = self.indentation_spaces * depth;
        member_range.col_start.0 != expected_column
    }
}

impl Rule for IN3Rule {
    fn name() -> &'static str {
        "IN3"
    }
    fn description() -> &'static str {
        "Previous line contains an openning brace and current line is not one\
         level of indentation ahead of past line"
    }
}

// IN6: Continuation Line
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct ContinuationLineOptions {
    pub indentation_spaces: u32,
}

pub struct ContinuationLineRule {
    pub enabled: bool,
    pub indentation_spaces: u32,
}

impl ContinuationLineRule {
    pub fn from_options(options: &Option<ContinuationLineOptions>) -> ContinuationLineRule {
        match options {
            Some(continuation_line) => ContinuationLineRule {
                enabled: true,
                indentation_spaces: continuation_line.indentation_spaces,
            },
            None => ContinuationLineRule {
                enabled: false,
                indentation_spaces: 0,
            },
        }
    }

    pub fn check(&self, acc: &mut Vec<LocalDMLError>, lines: &[&str]) {
        if !self.enabled {
            return;
        }

        let arithmetic_operators = ["+", "-", "*", "/", "%", "="];
        let comparison_operators = ["==", "!=", "<", ">", "<=", ">="];
        let logical_operators = ["&&", "||"];
        let bitwise_operators = ["&", "|", "<<", ">>"];

        let operators = [
            &arithmetic_operators[..],
            &comparison_operators[..],
            &logical_operators[..],
            &bitwise_operators[..],
        ];

        for (i, line) in lines.iter().enumerate() {
            if let Some(last_char) = line.trim().chars().last() {
                if operators.iter().any(|ops| ops.contains(&last_char.to_string().as_str())) {
                    let next_line = lines.get(i + 1);
                    if let Some(next_line) = next_line {
                        let expected_indent = line.chars().take_while(|c| c.is_whitespace()).count() + self.indentation_spaces as usize;
                        let actual_indent = next_line.chars().take_while(|c| c.is_whitespace()).count();
                        if actual_indent != expected_indent {
                            let msg = ContinuationLineRule::description().to_owned();
                            let dmlerror = LocalDMLError {
                                range: Range::new(
                                    Row::new_zero_indexed((i + 1) as u32),
                                    Row::new_zero_indexed((i + 1) as u32),
                                    Column::new_zero_indexed(0),
                                    Column::new_zero_indexed(next_line.len() as u32)
                                ),
                                description: msg,
                            };
                            acc.push(dmlerror);
                        }
                    }
                }
            }
        }
    }
}

impl Rule for ContinuationLineRule {
    fn name() -> &'static str {
        "CONTINUATION_LINE"
    }

    fn description() -> &'static str {
        "Continuation line not indented correctly"
    }
}

pub struct IN9Rule {
    pub enabled: bool,
    indentation_spaces: u32
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct IN9Options {
    pub indentation_spaces: u32,
}
pub struct IN9Args<'a> {
    case_range: ZeroRange,
    expected_depth: &'a mut u32,
}

impl IN9Args<'_> {
    pub fn from_switch_case<'a>(node: &SwitchCase, depth: &'a mut u32) -> Option<IN9Args<'a>> {
        match node {
            SwitchCase::Case(_, _, _) |
            SwitchCase::Default(_, _) => {},
            SwitchCase::Statement(statement) => {
                if let Content::Some(ref content) = *statement.content {
                    if let statement::StatementContent::Compound(_) = content {
                        return None;
                    }
                    *depth += 1;
                }
            },
            SwitchCase::HashIf(_) => {
                return None;
            }
        }

        Some(IN9Args {
            case_range: node.range(),
            expected_depth: depth
        })

    }
}

impl IN9Rule {
    pub fn from_options(options: &Option<IN9Options>) -> IN9Rule {
        match options {
            Some(options) => IN9Rule {
                enabled: true,
                indentation_spaces: options.indentation_spaces
            },
            None => IN9Rule {
                enabled: false,
                indentation_spaces: 0
            }
        }
    }
    pub fn check<'a>(&self, acc: &mut Vec<LocalDMLError>,
        args: Option<IN9Args<'a>>)
    {
        if !self.enabled { return; }
        let Some(args) = args else { return; };
        if self.indentation_is_not_aligned(args.case_range, *args.expected_depth) {
            let dmlerror = LocalDMLError {
                range: args.case_range,
                description: Self::description().to_string(),
            };
            acc.push(dmlerror);
        }
    }
    fn indentation_is_not_aligned(&self, member_range: ZeroRange, depth: u32) -> bool {
        // Implicit IN1
        let expected_column = self.indentation_spaces * depth;
        print!("{:#?}", expected_column);
        member_range.col_start.0 != expected_column
    }
}

impl Rule for IN9Rule {
    fn name() -> &'static str {
        "IN9"
    }
    fn description() -> &'static str {
        "Case labels are indented one level less than surrounding lines, \
         so that they are on the same level as the switch statement"
    }
}

// IN10: Indentation in empty loop
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct IN10Options {
    pub indentation_spaces: u32,
}

pub struct IN10Rule {
    pub enabled: bool,
    indentation_spaces: u32
}

impl IN10Rule {
    pub fn from_options(options: &Option<IN10Options>) -> IN10Rule {
        match options {
            Some(options) => IN10Rule {
                enabled: true,
                indentation_spaces: options.indentation_spaces,
            },
            None => IN10Rule {
                enabled: false,
                indentation_spaces: 0,
            },
        }
    }

    pub fn check(&self, acc: &mut Vec<LocalDMLError>, lines: &[&str]) {
        if !self.enabled {
            return;
        }

        for (i, line) in lines.iter().enumerate() {
            if line.trim().is_empty() {
                continue;
            }
            if line.trim().starts_with("for") || line.trim().starts_with("while") {
                let indentation = line.chars().take_while(|c| c.is_whitespace()).count();
                if let Some(next_line) = lines.get(i + 1) {
                    let next_line_trimmed = next_line.trim();
                    if next_line_trimmed == ";" {
                        let next_line_indentation = next_line.chars().take_while(|c| c.is_whitespace()).count();
                        if next_line_indentation != indentation + self.indentation_spaces as usize {
                            let msg = IN10Rule::description().to_owned();
                            let dmlerror = LocalDMLError {
                                range: Range::new(
                                    Row::new_zero_indexed((i + 1) as u32),
                                    Row::new_zero_indexed((i + 1) as u32),
                                    Column::new_zero_indexed(0),
                                    Column::new_zero_indexed(next_line.len() as u32)
                                ),
                                description: msg,
                            };
                            acc.push(dmlerror);
                        }
                    }
                }
            }
        }
    }
}

impl Rule for IN10Rule {
    fn name() -> &'static str {
        "IN10_INDENTATION_EMPTY_LOOP"
    }

    fn description() -> &'static str {
        "When the body of a while or for loop is left empty, \
        indent the semicolon to the appropriate statement level"
    }
}
