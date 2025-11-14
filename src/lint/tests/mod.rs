use std::path::Path;
use std::str::FromStr;
use crate::{analysis::{parsing::{parser::FileInfo, structure::{self, TopAst}}, FileSpec}, vfs::TextFile};

pub fn create_ast_from_snippet(source: &str) -> TopAst {
    use logos::Logos;
    use crate::analysis::parsing::lexer::TokenKind;
    use crate::analysis::parsing::parser::FileParser;
    let lexer = TokenKind::lexer(source);
    let mut fparser = FileParser::new(lexer);
    let mut parse_state = FileInfo::default();
    let file_result =  &TextFile::from_str(source);
    assert!(file_result.is_ok());
    let file = file_result.clone().unwrap();
    let filespec = FileSpec {
        path: Path::new("test.txt"), file: &file
    };
    structure::parse_toplevel(&mut fparser, &mut parse_state, filespec)
}

pub mod basic_tests {
    use crate::lint::tests::create_ast_from_snippet;

    pub static SOURCE: &str = "
    dml 1.4;

    bank sb_cr {
        group monitor {    

            register MKTME_KEYID_MASK {
                method get() -> (uint64) {
                    local uint64 physical_address_mask = mse.srv10nm_mse_mktme.get_key_addr_mask();
                    this.Mask.set(physical_address_mask);
                    this.function_with_args('some_string',
                                    integer,
                                    floater);
                    return this.val;
                }
            }

            register TDX_KEYID_MASK {
                method get() -> (uint64) {
                    local uint64 tdx_keyid_mask = mse.srv10nm_mse_tdx.get_key_addr_mask();
                    local uint64 some_uint = (is_this_real) ? then_you_might_like_this_value : or_this_one;
                    this.Mask.set(tdx_keyid_mask);
                    return this.val;
                }
            }
        }
    }   

    /*
        This is ONEEEE VEEEEEERY LLOOOOOOONG COOOMMMEENTT ON A SINGLEEEE LINEEEEEEEEEEEEEE
        and ANOTHEEEER VEEEEEERY LLOOOOOOONG COOOMMMEENTT ON A SINGLEEEE LINEEEEEEEEEEEEEE
    */

    ";


    // Tests both that the example Cfg parses, and that it is the default Cfg
    pub static EXAMPLE_CFG: &str = "/example_files/example_lint_cfg.json";
    #[test]
    fn test_example_lintcfg() {
        use crate::lint::{parse_lint_cfg, LintCfg};
        let example_path = format!("{}{}",
                                   env!("CARGO_MANIFEST_DIR"),
                                   EXAMPLE_CFG);
        let example_cfg = parse_lint_cfg(example_path.into()).unwrap();
        assert_eq!(example_cfg, LintCfg::default());
    }

    #[test]
    #[ignore]
    fn test_main() {
        use crate::lint::{begin_style_check, LintCfg};
        use crate::lint::rules:: instantiate_rules;
        let ast = create_ast_from_snippet(SOURCE);
        let cfg = LintCfg::default();
        let rules = instantiate_rules(&cfg);
        let _lint_errors = begin_style_check(ast, SOURCE.to_string(), &rules);
        assert!(_lint_errors.is_ok());
        assert!(!_lint_errors.unwrap().is_empty());
    }
}

pub mod autofix;
