use std::convert::TryInto;

use crate::analysis::parsing::{statement::CompoundContent,
                               structure::ObjectStatementsContent,
                               types::{LayoutContent, StructTypeContent}};
use crate::span::{Range, ZeroIndexed, Row, Column};
use crate::analysis::LocalDMLError;
use crate::analysis::parsing::tree::{ZeroRange, TreeElement};
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

#[cfg(test)]
pub mod tests {

    use crate::lint::rules::tests::assert_snippet;
    use crate::lint::rules::instantiate_rules;
    use crate::lint::LintCfg;
    use crate::lint::LongLineOptions;
    use std::convert::TryInto;

    //  Line length can be configured to a maximum
    //(defaults to 80, feature disabled)
    pub static LONG_LINE: &str = "
param some_parameter_name_in_this_device = some_long_name_bank.some_long_name_group.SOME_REGISTER_NAME;
";
    #[test]
    fn style_check_long_line() {
        let mut cfg = LintCfg::default();
        let mut rules = instantiate_rules(&cfg);
        assert_snippet(LONG_LINE, 1, &rules);
        // Test rule disable
        cfg.long_lines = None;
        rules = instantiate_rules(&cfg);
        assert_snippet(LONG_LINE, 0, &rules);
        // Test lower max_length
        cfg.long_lines = Some(LongLineOptions{
            max_length: (LONG_LINE.len()-3).try_into().unwrap()
        });
        rules = instantiate_rules(&cfg);
        assert_snippet(LONG_LINE, 1, &rules);
    }
}
