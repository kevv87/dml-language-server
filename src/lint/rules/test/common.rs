use crate::analysis::LocalDMLError;
use crate::lint::LintCfg;
use crate::lint::rules::{CurrentRules, instantiate_rules};
use crate::lint::rules::tests::{run_linter};

pub fn set_up() -> CurrentRules {
    let cfg = LintCfg::default();
    instantiate_rules(&cfg)
}

pub fn assert_indentation(
    code: &str, expected_errors: usize, rules: CurrentRules)
{
    let lint_errors = run_linter(code, &rules);
    let Ok(ref lint_errors) = lint_errors else {
        panic!();
    };
    let mut indent_errors: Vec<&LocalDMLError> = vec!();
    for error in lint_errors {
        indent_errors.push(error);
    }
    assert_eq!(indent_errors.len(), expected_errors, "{:#?}", lint_errors);
}
