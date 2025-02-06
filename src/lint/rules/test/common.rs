use crate::lint::LintCfg;
use crate::lint::rules::CurrentRules;
use crate::lint::rules::instantiate_rules;

pub fn set_up() -> CurrentRules {
    let cfg = LintCfg::default();
    instantiate_rules(&cfg)
}
