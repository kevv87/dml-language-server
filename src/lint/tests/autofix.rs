use lsp_types::{Position, Range, TextEdit};

use crate::lint::tests::create_ast_from_snippet;
use crate::lint::{begin_style_check, LintCfg};
use crate::lint::rules::{ instantiate_rules, RuleType};
use crate::lint::rules::tests::common::run_linter;

pub static SOURCE: &str = "
bank sb_cr {
    group monitor {    
        register MKTME_KEYID_MASK {
            method get() -> (uint64) {
                return this.val;
            }
        }
    }
}   
";

#[test]
pub fn test_01_dml_style_error_reported_has_fix_field(){
    let ast = create_ast_from_snippet(SOURCE);
    let cfg = LintCfg::default();
    let rules = instantiate_rules(&cfg);
    let lint_errors = begin_style_check(ast, SOURCE.to_string(), &rules);
    assert!(lint_errors.is_ok());
    
    let errors = lint_errors.unwrap();
    assert!(!errors.is_empty());

    for error in errors {
        assert!(error.fix.is_none());
    }
}

pub static SIMPLE_SP_ERR: &str = "method this_is_some_method() {return 0;}";

#[test]
pub fn test_02_simple_spacing_error_has_correct_fix() {
    let cfg = LintCfg::default();
    let rules = instantiate_rules(&cfg);
    let lint_errors = run_linter(SIMPLE_SP_ERR, &rules);
    assert!(lint_errors.is_ok());
    
    let errors = lint_errors.unwrap();
    assert!(!errors.is_empty());

    let expected_fix = vec![
        TextEdit {
            range: Range::new(
                Position::new(0, 30),
                Position::new(0, 30)
            ),
            new_text: " ".to_string(),
        },
        TextEdit {
            range: Range::new(
                Position::new(0, 39),
                Position::new(0, 39)
            ),
            new_text: " ".to_string(),
        },
    ];
    for error in errors {
        match error.rule_type {
            RuleType::SpBraces => {
                if let Some(fix) = &error.fix {
                    assert!(expected_fix.contains(fix), 
                        "Provided fix not expected: {:?}", fix);
                }
            },
            _ => print!("Got {:?} error, skipping", error.rule_type),
        }
    }
}



// TODO: We should also check that LinterAnalysis::new() returns what we need
