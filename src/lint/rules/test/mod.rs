#[cfg(test)]
pub mod indentation_tests {

use crate::lint::LintCfg;
use crate::lint::rules::tests::{run_linter, assert_snippet};
use crate::lint::rules::instantiate_rules;
use crate::lint::rules::CurrentRules;
use crate::analysis::LocalDMLError;

fn set_up() -> CurrentRules {
    let cfg = LintCfg::default();
    instantiate_rules(&cfg)
}

fn assert_indentation(
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

pub static IN3_FUNCTION_CONTENTS_CORRECT_INDENT: &str = "
method some_function(int a) {
    return 0;
}
";
#[test]
fn in3_function_contents_should_indent() {
    let rules = set_up();
    assert_indentation(IN3_FUNCTION_CONTENTS_CORRECT_INDENT, 0, rules);
}

pub static IN3_ONE_LINE_NO_INDENT: &str = "
method some_function(int a) { return 0; }
";
#[test]
fn in3_one_line_no_indent() {
    let rules = set_up();
    assert_indentation(IN3_ONE_LINE_NO_INDENT, 0, rules);
}

pub static IN3_FUNCTION_CONTENTS_NO_INDENT: &str = "
method some_function(int a) {
return a;
}
";
#[test]
fn in3_function_contents_no_indent() {
    let rules = set_up();
    assert_indentation(IN3_FUNCTION_CONTENTS_NO_INDENT, 1, rules);
}

pub static IN3_FUNCTION_PARAMS_BREAKED_AND_NO_INDENT: &str = "
method some_function(int a,
                     int b) {
return a;
}
";
#[test]
fn in3_function_params_breaked_and_no_indent() {
    let rules = set_up();
    assert_indentation(IN3_FUNCTION_PARAMS_BREAKED_AND_NO_INDENT, 1, rules);
}

pub static IN3_FUNCTION_PARAMS_BADLY_BREAKED_AND_NO_INDENT: &str = "
method some_function(int a,
    int b)
{
return a;
}
";
#[test]
fn in3_function_params_badly_breaked_and_no_indent() {
    let rules = set_up();
    assert_indentation(IN3_FUNCTION_PARAMS_BADLY_BREAKED_AND_NO_INDENT, 1, rules);
}

pub static IN3_INLINE_FUNCTION_PARAMS_BADLY_BREAKED_AND_NO_INDENT: &str = "
inline method some_function(int a,
    int b)
{
return a;
}
";
#[test]
fn in3_inline_function_params_badly_breaked_and_no_indent() {
    let rules = set_up();
    assert_indentation(IN3_INLINE_FUNCTION_PARAMS_BADLY_BREAKED_AND_NO_INDENT, 1, rules);
}

}
