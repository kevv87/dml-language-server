pub mod spacing;
pub mod indentation;
pub mod test;

use spacing::{SpBracesRule,
    SpPunctRule, NspFunparRule, NspInparenRule,
    NspUnaryRule, NspTrailingRule};
use indentation::{LongLinesRule, IN3Rule};
use crate::lint::LintCfg;

pub struct CurrentRules {
    pub sp_brace: SpBracesRule,
    pub sp_punct: SpPunctRule,
    pub nsp_funpar: NspFunparRule,
    pub nsp_inparen: NspInparenRule,
    pub nsp_unary: NspUnaryRule,
    pub nsp_trailing: NspTrailingRule,
    pub long_lines: LongLinesRule,
    pub in3: IN3Rule,
}

pub fn  instantiate_rules(cfg: &LintCfg) -> CurrentRules {
    CurrentRules {
        sp_brace: SpBracesRule { enabled: cfg.sp_brace.is_some() },
        sp_punct: SpPunctRule { enabled: cfg.sp_punct.is_some() },
        nsp_funpar: NspFunparRule { enabled: cfg.nsp_funpar.is_some() },
        nsp_inparen: NspInparenRule { enabled: cfg.nsp_inparen.is_some() },
        nsp_unary: NspUnaryRule { enabled: cfg.nsp_unary.is_some() },
        nsp_trailing: NspTrailingRule { enabled: cfg.nsp_trailing.is_some() },
        long_lines: LongLinesRule::from_options(&cfg.long_lines),
        in3: IN3Rule::from_options(&cfg.in3),
    }
}

// struct/trait generic_rule
pub trait Rule {
    fn name() -> &'static str;
    fn description() -> &'static str;
}

pub mod tests {

use crate::lint::tests::create_ast_from_snippet;
use crate::lint::begin_style_check;
use crate::lint::rules::CurrentRules;
use crate::analysis::LocalDMLError;
use crate::vfs::Error;

pub fn run_linter(source_code: &str, rules: &CurrentRules)
    -> Result<Vec<LocalDMLError>, Error>
{
    print!("\nSnippet to test on:\n{}\n", source_code);
    let ast = create_ast_from_snippet(source_code);
    print!("Resulting AST:\n{:#?}\n", ast);
    begin_style_check(ast, source_code.to_string(), rules)
}

pub fn assert_snippet(source_code: &str, expected_errors: usize, rules: &CurrentRules) {
    let lint_errors = run_linter(source_code, rules);
    assert!(lint_errors.is_ok());
    assert_eq!(lint_errors.clone().unwrap().len(), expected_errors,
               "{:#?}", lint_errors);
}

}
