use std::convert::TryInto;

use crate::{analysis::LocalDMLError, span::{Range, ZeroIndexed}};
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
