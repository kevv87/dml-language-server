use itertools::izip;
use std::convert::TryInto;
use serde::{Deserialize, Serialize};
use crate::analysis::parsing::types::{BitfieldsContent, LayoutContent,
                                      StructTypeContent};
use crate::lint::rules::Rule;
use crate::analysis::LocalDMLError;
use crate::analysis::parsing::tree::{TreeElement, ZeroRange};
use crate::analysis::parsing::expression::{FunctionCallContent, IndexContent,
                                           PostUnaryExpressionContent,
                                           UnaryExpressionContent};
use crate::analysis::parsing::statement::{CompoundContent,
                                          ExpressionStmtContent,
                                          IfContent, VariableDeclContent};
use crate::analysis::parsing::structure::{MethodContent,
                                          ObjectStatementsContent};

use crate::span::{ZeroIndexed, Range};

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct SpBraceOptions {}

pub struct SpBracesRule {
    pub enabled: bool,
}
pub struct SpBracesArgs {
    body_start: ZeroRange,
    body_end: ZeroRange,
    lbrace: ZeroRange,
    rbrace: ZeroRange,
}
impl SpBracesArgs {
    pub fn from_compound(node: &CompoundContent) -> Option<SpBracesArgs> {
        if node.statements.is_empty() {
            return None;
        }
        Some(SpBracesArgs {
            body_start: node.statements.first().unwrap().range(),
            body_end: node.statements.last().unwrap().range(),
            lbrace: node.lbrace.range(),
            rbrace: node.rbrace.range(),
        })
    }
    pub fn from_obj_stmts(node: &ObjectStatementsContent)
                          -> Option<SpBracesArgs> {
        if let ObjectStatementsContent::List(l_brace,
                                             declarations,
                                             r_brace) = node {
            if declarations.is_empty() {
                return None;
            }
            return Some(SpBracesArgs {
                body_start: declarations.first().unwrap().range(),
                body_end: declarations.last().unwrap().range(),
                lbrace: l_brace.range(),
                rbrace: r_brace.range(),
            })
        } else {
            None
        }
    }
    pub fn from_struct_type_content(node: &StructTypeContent)
                                    -> Option<SpBracesArgs> {
        if node.members.is_empty() {
            return None;
        }
        Some(SpBracesArgs {
            body_start: node.members.first().unwrap().range(),
            body_end: node.members.last().unwrap().range(),
            lbrace: node.lbrace.range(),
            rbrace: node.rbrace.range(),
        })
    }
    pub fn from_layout_content(node: &LayoutContent) -> Option<SpBracesArgs> {
        if node.fields.is_empty() {
            return None;
        }
        Some(SpBracesArgs {
            body_start: node.fields.first().unwrap().range(),
            body_end: node.fields.last().unwrap().range(),
            lbrace: node.lbrace.range(),
            rbrace: node.rbrace.range(),
        })
    }
    pub fn from_bitfields_content(node: &BitfieldsContent)
                                  -> Option<SpBracesArgs> {
        if node.fields.is_empty() {
            return None;
        }
        Some(SpBracesArgs {
            body_start: node.fields.first().unwrap().range(),
            body_end: node.fields.last().unwrap().range(),
            lbrace: node.lbrace.range(),
            rbrace: node.rbrace.range(),
        })
    }
}

impl SpBracesRule {
    pub fn check(&self, acc: &mut Vec<LocalDMLError>,
        ranges: Option<SpBracesArgs>) {
        if !self.enabled { return; }
        if let Some(location) = ranges {
            if (location.lbrace.row_end == location.body_start.row_start)
                && (location.lbrace.col_end == location.body_start.col_start) {
                let dmlerror = LocalDMLError {
                    range: location.lbrace,
                    description: Self::description().to_string(),
                };
                acc.push(dmlerror);
            }
            if (location.rbrace.row_start == location.body_end.row_end)
                && (location.rbrace.col_start == location.body_end.col_end) {
                let dmlerror = LocalDMLError {
                    range: location.rbrace,
                    description: Self::description().to_string(),
                };
                acc.push(dmlerror);
            }
        }
    }
}

impl Rule for SpBracesRule {
    fn name() -> &'static str {
        "SP_BRACE"
    }
    fn description() -> &'static str {
        "Missing space around brace"
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct SpPunctOptions {}

pub struct SpPunctRule {
    pub enabled: bool,
}
pub struct SpPunctArgs {
    before_range_list: Vec<Range<ZeroIndexed>>,
    punct_range_list: Vec<Range<ZeroIndexed>>,
    after_range_list: Vec<Option<Range<ZeroIndexed>>>,
}
impl SpPunctArgs {
    pub fn from_method(node: &MethodContent) -> Option<SpPunctArgs> {
        let mut before_range_list = vec![];
        let mut punct_range_list = vec![];
        let mut after_range_list = vec![];
        let mut iterator = node.arguments.iter().peekable();

        while let Some((arg_decl, comma)) = iterator.next() {
            if let Some(comma_token) = comma {
                before_range_list.push(arg_decl.range());
                punct_range_list.push(comma_token.range());
                if let Some((next_arg_decl, _)) = iterator.peek() {
                    after_range_list.push(Some(next_arg_decl.range()));
                } else {
                    after_range_list.push(None);
                }
            }
        }

        Some(SpPunctArgs {
            before_range_list,
            punct_range_list,
            after_range_list,
        })
    }
    pub fn from_function_call(node: &FunctionCallContent)
                              -> Option<SpPunctArgs> {
        let mut before_range_list = vec![];
        let mut punct_range_list = vec![];
        let mut after_range_list = vec![];
        let mut iterator = node.arguments.iter().peekable();

        while let Some((expression, comma)) = iterator.next() {
            if let Some(comma_token) = comma {
                before_range_list.push(expression.range());
                punct_range_list.push(comma_token.range());
                if let Some((next_expression, _)) = iterator.peek() {
                    after_range_list.push(Some(next_expression.range()));
                } else {
                    after_range_list.push(None);
                }
            }
        }

        Some(SpPunctArgs {
            before_range_list,
            punct_range_list,
            after_range_list,
        })
    }
    pub fn from_expression_stmt(node: &ExpressionStmtContent)
                                -> Option<SpPunctArgs> {
        let mut before_range_list = vec![];
        let mut punct_range_list = vec![];
        let mut after_range_list = vec![];

        before_range_list.push(node.expression.range());
        punct_range_list.push(node.semi.range());
        after_range_list.push(None);

        Some(SpPunctArgs {
            before_range_list,
            punct_range_list,
            after_range_list,
        })
    }
    pub fn from_variable_decl(node: &VariableDeclContent)
                              -> Option<SpPunctArgs> {
        let mut before_range_list = vec![];
        let mut punct_range_list = vec![];
        let mut after_range_list = vec![];

        if let Some(initializer) = node.initializer.as_ref() {
            before_range_list.push(initializer.1.range());
        } else {
            before_range_list.push(node.decls.range());
        }
        punct_range_list.push(node.semi.range());
        after_range_list.push(None);

        Some(SpPunctArgs {
            before_range_list,
            punct_range_list,
            after_range_list,
        })
    }
}

impl SpPunctRule {
    pub fn check(&self, acc: &mut Vec<LocalDMLError>,
        ranges: Option<SpPunctArgs>) {
        if !self.enabled { return; }
        if let Some(args) = ranges {
            for (before_range, punct_range, after_range) in
                izip!(args.before_range_list,
                      args.punct_range_list,
                      args.after_range_list) {
                if (before_range.row_end != punct_range.row_start)
                    || (before_range.col_end != punct_range.col_start) {
                    let error_range = Range::new(
                        before_range.row_end, punct_range.row_start,
                        before_range.col_end, punct_range.col_start
                    );
                    let dmlerror = LocalDMLError {
                        range: error_range,
                        description: Self::description().to_string(),
                    };
                    acc.push(dmlerror);
                }

                if after_range.is_none() {continue;}

                if (punct_range.row_end == after_range.unwrap().row_start)
                    && (punct_range.col_end == after_range.unwrap().col_start) {
                    let error_range = Range::new(
                        punct_range.row_start, after_range.unwrap().row_end,
                        punct_range.col_start, after_range.unwrap().col_end,
                    );
                    let dmlerror = LocalDMLError {
                        range: error_range,
                        description: Self::description().to_string(),
                    };
                    acc.push(dmlerror);
                }
            }
        }
    }
}

impl Rule for SpPunctRule {
    fn name() -> &'static str {
        "SP_PUNCT"
    }
    fn description() -> &'static str {
        "Missing space after punctuation mark"
    }
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct NspFunparOptions {}

pub struct NspFunparRule {
    pub enabled: bool,
}
 // Single ZeroRange required as input for this rule
pub type NspFunparArgs = ZeroRange;
impl NspFunparArgs {
    fn found_gap(fn_name: &ZeroRange, lparen: &ZeroRange)
                 -> Option<NspFunparArgs> {
        if (fn_name.row_end != lparen.row_start)
        || (fn_name.col_end != lparen.col_start) {
            Some(NspFunparArgs {
                row_start: fn_name.row_end,
                row_end: lparen.row_start,
                col_start: fn_name.col_end,
                col_end: lparen.col_start,
            })
        } else { None }
    }
    pub fn from_method(node: &MethodContent) -> Option<NspFunparArgs> {
        Self::found_gap(&node.name.range(), &node.lparen.range())
    }
    pub fn from_function_call(node: &FunctionCallContent)
                              -> Option<NspFunparArgs> {
        Self::found_gap(&node.fun.range(), &node.lparen.range())
    }
}
impl NspFunparRule {
    pub fn check(&self,
                 acc: &mut Vec<LocalDMLError>,
                 range: Option<NspFunparArgs>) {
        if !self.enabled { return; }
        if let Some(gap) = range {
            let dmlerror = LocalDMLError {
                range: gap,
                description: Self::description().to_string(),
            };
            acc.push(dmlerror);
        }
    }
}
impl Rule for NspFunparRule {
    fn name() -> &'static str {
        "NSP_FUNPAR"
    }
    fn description() -> &'static str {
        "There should be no space between a method/function name and its opening parenthesis."
    }
}


#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct NspInparenOptions {}

pub struct NspInparenRule {
    pub enabled: bool,
}
pub struct NspInparenArgs {
    opening: ZeroRange,
    content_start: ZeroRange,
    content_end: ZeroRange,
    closing: ZeroRange,
}
impl NspInparenArgs {
    pub fn from_method(node: &MethodContent) -> Option<NspInparenArgs> {
        let content_start_range;
        let content_end_range;
        if node.arguments.is_empty() {
            content_start_range = node.rparen.range();
            content_end_range = node.lparen.range();
        } else {
            content_start_range = node.arguments.first().unwrap().range();
            content_end_range = node.arguments.last().unwrap().range();
        }
        Some(NspInparenArgs {
            opening: node.lparen.range(),
            content_start: content_start_range,
            content_end: content_end_range,
            closing: node.rparen.range(),
        })
    }
    pub fn from_function_call(node: &FunctionCallContent)
                              -> Option<NspInparenArgs> {
        let content_start_range;
        let content_end_range;
        if node.arguments.is_empty() {
            content_start_range = node.rparen.range();
            content_end_range = node.lparen.range();
        } else {
            content_start_range = node.arguments.first().unwrap().range();
            content_end_range = node.arguments.last().unwrap().range();
        }
        Some(NspInparenArgs {
            opening: node.lparen.range(),
            content_start: content_start_range,
            content_end: content_end_range,
            closing: node.rparen.range(),
        })
    }
    pub fn from_if(node: &IfContent) -> Option<NspInparenArgs> {
        Some(NspInparenArgs {
            opening: node.lparen.range(),
            content_start: node.cond.range(),
            content_end: node.cond.range(),
            closing: node.rparen.range(),
        })
    }
    pub fn from_index(node: &IndexContent) -> Option<NspInparenArgs> {
        Some(NspInparenArgs {
            opening: node.lbracket.range(),
            content_start: node.index.range(),
            content_end: node.index.range(),
            closing: node.rbracket.range(),
        })
    }
}
impl NspInparenRule {
    pub fn check(&self,
                 acc: &mut Vec<LocalDMLError>,
                 ranges: Option<NspInparenArgs>) {
        if !self.enabled { return; }
        if let Some(location) =  ranges {
            if (location.opening.row_end == location.content_start.row_start)
                && (location.opening.col_end != location.content_start.col_start) { 
                let mut gap = location.opening;
                gap.col_start = location.opening.col_end;
                gap.col_end = location.content_start.col_start;
                let dmlerror = LocalDMLError {
                    range: gap,
                    description: Self::description().to_string(),
                };
                acc.push(dmlerror);
            }
            if (location.closing.row_start == location.content_end.row_end)
                && (location.closing.col_start != location.content_end.col_end) { 
                let mut gap = location.closing;
                gap.col_end = location.closing.col_start;
                gap.col_start = location.content_end.col_end;
                let dmlerror = LocalDMLError {
                    range: gap,
                    description: Self::description().to_string(),
                };
                acc.push(dmlerror);
            }
        }
    }
}
impl Rule for NspInparenRule {
    fn name() -> &'static str {
        "NSP_INPAREN"
    }
    fn description() -> &'static str {
        "There should be no space after opening or before closing () / []"
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct NspUnaryOptions {}

pub struct NspUnaryRule {
    pub enabled: bool,
}
// Single ZeroRange required as input for this rule
pub type NspUnaryArgs = ZeroRange;
impl NspUnaryArgs {
    pub fn from_unary_expr(node: &UnaryExpressionContent)
                           -> Option<NspUnaryArgs> {
        let mut gap = node.range();
        gap.col_start = node.operation.range().col_end;
        gap.col_end = node.expr.range().col_start;
        if gap.col_end != gap.col_start {
            Some(gap)
        } else { None }
    }
    pub fn from_postunary_expr(node: &PostUnaryExpressionContent)
                               -> Option<NspUnaryArgs> {
        let mut gap = node.range();
        gap.col_start = node.expr.range().col_end;
        gap.col_end = node.operation.range().col_start;
        if gap.col_end != gap.col_start {
            Some(gap)
        } else { None }
    }
}
impl NspUnaryRule {
    pub fn check(&self,
                 acc: &mut Vec<LocalDMLError>,
                 range: Option<NspUnaryArgs>) {
        if !self.enabled { return; }
        if let Some(gap) = range {
            let dmlerror = LocalDMLError {
                range: gap,
                description: Self::description().to_string(),
            };
            acc.push(dmlerror);
        }
    }
}
impl Rule for NspUnaryRule {
    fn name() -> &'static str {
        "NSP_UNARY"
    }
    fn description() -> &'static str {
        "There should be no space between unary operator and its operand"
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct NspTrailingOptions {}

pub struct NspTrailingRule {
    pub enabled: bool,
}
impl NspTrailingRule {
    pub fn check(&self, acc: &mut Vec<LocalDMLError>, row: usize, line: &str) {
        if !self.enabled { return; }
        let len = line.len().try_into().unwrap();
        let row_u32 = row.try_into().unwrap();
        let tokens_end = line.trim_end().len().try_into().unwrap();
        if tokens_end < len {
            let dmlerror = LocalDMLError {
                range: Range::<ZeroIndexed>::from_u32(row_u32,
                                                      row_u32,
                                                      tokens_end,
                                                      len),
                description: Self::description().to_string(),
            };
            acc.push(dmlerror);
        }
    }
}
impl Rule for NspTrailingRule {
    fn name() -> &'static str {
        "NSP_TRAILING"
    }
    fn description() -> &'static str {
        "Found trailing whitespace on row"
    }
}

#[cfg(test)]
pub mod tests {

    use crate::lint::rules::tests::assert_snippet;
    use crate::lint::rules::instantiate_rules;
    use crate::lint::LintCfg;

    // Put whitespace (space or newline):
    //  SP.reserved around reserved words, such as if, else, default,
    //  size, const and in, except when a reserved word is used as an identifier
    //  (e.g., local uint8 *data;)
    pub static SP_RESERVED: &str = "
method this_is_some_method() {
    local int this_some_integer = 0x666;
    if(this_some_integer == 0x666)
        return;
}
";

    //  SP.braces around braces ({ and })
    pub static SP_BRACES: &str = "
method this_is_some_method() {return 0;}

method this_is_empty_method() { }

bank pcie_config {register command {field mem {
            method pcie_write(uint64 value) {
                if (value != 0) {value = value + 1;
                }
                default(value);
                map_memory_alt();}
}}}
";
    #[test]
    fn style_check_sp_braces() {
        let mut cfg = LintCfg::default();
        let mut rules = instantiate_rules(&cfg);
        assert_snippet(SP_BRACES, 8, &rules);
        // Test rule disable
        cfg.sp_brace = None;
        rules = instantiate_rules(&cfg);
        assert_snippet(SP_BRACES, 0, &rules);

    }

    pub static SP_BRACES_02: &str = "
typedef struct {uint16 idx;} hqm_cq_list_release_ctx_t;

typedef layout \"little-endian\" {bitfields 8 {uint2 rsvd @ [7:6];
        uint1 error_f          @ [5:5];
        uint1 int_arm          @ [4:4];
        uint1 qe_valid         @ [3:3];
        uint1 qe_frag          @ [2:2];
        uint1 qe_comp          @ [1:1];
        uint1 cq_token         @ [0:0];} byte;} prod_qe_cmd_t;
";
    #[test]
    fn style_check_sp_braces_02() {
        let mut cfg = LintCfg::default();
        let mut rules = instantiate_rules(&cfg);
        assert_snippet(SP_BRACES_02, 6, &rules);
        // Test rule disable
        cfg.sp_brace = None;
        rules = instantiate_rules(&cfg);
        assert_snippet(SP_BRACES_02, 0, &rules);

    }

    //  SP.binop around binary operators except the dereferencing operators dot
    //  (a.b) and arrow (a->b)
    pub static SP_BINOP: &str = "
method this_is_some_method() {
    local int this_some_integer = 5+6;
    if (this_some_integer == 0x666)
        this_some_integer = this.val;
}
";

    //  SP.ternary around ? and : in the ternary ?: operator
    pub static SP_TERNARY: &str = "
method this_is_some_method(bool flag) {
    local int this_some_integer = (flag?5:7));
}
";

    //  SP.punct after but not before colon, semicolon and comma
    pub static SP_PUNCT: &str = "
method this_is_some_method(bool flag ,int8 var) {
    local int this_some_integer = 0x666 ;
    if(this_some_integer == 0x666)
        return;
    some_func(arg1 ,arg2 ,arg3 ,arg4);
}
";
    #[test]
    fn style_check_sp_punct_rule() {
        let mut cfg = LintCfg::default();
        let mut rules = instantiate_rules(&cfg);
        assert_snippet(SP_PUNCT, 9, &rules);
        // Test rule disable
        cfg.sp_punct = None;
        rules = instantiate_rules(&cfg);
        assert_snippet(SP_PUNCT, 0, &rules);
    }

    //  SP.ptrdecl between a type and the * marking a pointer
    pub static SP_PTRDECL: &str = "
method this_is_some_method(conf_object_t* dummy_obj) {
    if(!dummy_obj)
        return;
}
";

    //  SP.comment around the comment delimiters //, /* and **/
    pub static SP_COMMENT: &str = "
/*Function
documentation*/
method this_is_some_method(conf_object_t *dummy_obj) {
    if(!dummy_obj)//Not null
        return;
}
";

    // There should be no space:
    //  NSP.funpar between a function/method name and its opening parenthesis
    pub static NSP_FUNPAR: &str = "
method this_is_some_method (conf_object_t *dummy_obj) {
    if(!dummy_obj)
        other_method_called ();
}
";
    #[test]
    fn style_check_nsp_funpar() {
        let mut cfg = LintCfg::default();
        let mut rules = instantiate_rules(&cfg);
        assert_snippet(NSP_FUNPAR, 2, &rules);
        // Test rule disable
        cfg.nsp_funpar = None;
        rules = instantiate_rules(&cfg);
        assert_snippet(NSP_FUNPAR, 0, &rules);
    }

    //  NSP.inparen immediately inside parentheses or brackets
    pub static NSP_INPAREN: &str = "
method this_is_some_method( conf_object_t *dummy_obj ) {
    if( !dummy_obj[ 0 ] )
        return;
}
";
    #[test]
    fn style_check_nsp_inparen() {
        let mut cfg = LintCfg::default();
        let mut rules = instantiate_rules(&cfg);
        assert_snippet(NSP_INPAREN, 6, &rules);
        // Test rule disable
        cfg.nsp_inparen = None;
        rules = instantiate_rules(&cfg);
        assert_snippet(NSP_INPAREN, 0, &rules);
    }

    //  NSP.unary between a unary operator and its operand
    pub static NSP_UNARY: &str = "
method this_is_some_method(conf_object_t *dummy_obj) {
    if(! dummy_obj)
        return;
    local uint64 p = & dummy_obj;
    p ++;
    -- p;
    local int64 neg = - 1;
}
";
    #[test]
    fn style_check_nsp_unary() {
        let mut cfg = LintCfg::default();
        let mut rules = instantiate_rules(&cfg);
        assert_snippet(NSP_UNARY, 5, &rules);
        // Test rule disable
        cfg.nsp_unary = None;
        rules = instantiate_rules(&cfg);
        assert_snippet(NSP_UNARY, 0, &rules);
    }

    //  NSP.ptrdecl after the * marking a pointer in a declaration
    pub static NSP_PTRDECL: &str = "
method this_is_some_method(conf_object_t * dummy_obj) {
    if(!dummy_obj)
        return;
}
";

    //  Adding trailing whitespace removal to spacing rules:
    //  no whitespaces should be left at the end of a line between the last token
    //  and the newline \n
    pub static NSP_TRAILING: &str = "
method this_is_some_method(int64 num) {
    local int this_some_integer = 0x666;           
    if (this_some_integer == 0x666)       
        return;  
}   
";
    #[test]
    fn style_check_nsp_trailing() {
        let mut cfg = LintCfg::default();
        let mut rules = instantiate_rules(&cfg);
        assert_snippet(NSP_TRAILING, 4, &rules);
        // Test rule disable
        cfg.nsp_trailing = None;
        rules = instantiate_rules(&cfg);
        assert_snippet(NSP_TRAILING, 0, &rules);
    }
}