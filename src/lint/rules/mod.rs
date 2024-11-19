pub mod spacing;
pub mod indentation;

use crate::lint::rules::spacing::{SpBracesRule,
    SpPunctRule, NspFunparRule, NspInparenRule,
    NspUnaryRule, NspTrailingRule};
use crate::lint::LongLineOptions;
use crate::lint::rules::indentation::LongLinesRule;
use crate::lint::LintCfg;

pub struct CurrentRules {
    pub sp_brace: SpBracesRule,
    pub sp_punct: SpPunctRule,
    pub nsp_funpar: NspFunparRule,
    pub nsp_inparen: NspInparenRule,
    pub nsp_unary: NspUnaryRule,
    pub nsp_trailing: NspTrailingRule,
    pub long_lines: LongLinesRule,
}

pub fn  instantiate_rules(cfg: &LintCfg) -> CurrentRules {
    CurrentRules {
        sp_brace: SpBracesRule { enabled: cfg.sp_brace.is_some() },
        sp_punct: SpPunctRule { enabled: cfg.sp_punct.is_some() },
        nsp_funpar: NspFunparRule { enabled: cfg.nsp_funpar.is_some() },
        nsp_inparen: NspInparenRule { enabled: cfg.nsp_inparen.is_some() },
        nsp_unary: NspUnaryRule { enabled: cfg.nsp_unary.is_some() },
        nsp_trailing: NspTrailingRule { enabled: cfg.nsp_trailing.is_some() },
        long_lines: LongLineOptions::into_rule(&cfg.long_lines),
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

    pub fn assert_snippet(source_code: &str,
                          expected_errors: usize,
                          rules: &CurrentRules) {
        print!("\nSnippet to test on:\n{}\n", source_code);
        let ast = create_ast_from_snippet(source_code);
        print!("Resulting AST:\n{:#?}\n", ast);
        let lint_errors = begin_style_check(ast,
                                            source_code.to_string(),
                                            rules);

        assert!(lint_errors.is_ok());
        assert_eq!(lint_errors.clone().unwrap().len(), expected_errors,
                   "{:#?}", lint_errors);
    }
}
