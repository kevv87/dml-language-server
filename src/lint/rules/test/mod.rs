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

pub static IN3_FULL_BANK_CORRECT_INDENT: &str = "
bank BankA {
    group GroupB {
        param some_param = this.REG_C;
        register REG_C[osdml_reg_idx < ...] is (some_template) {
            param other_param = 0;
            field Field_D {
                is osdml_write;
                method write_action(uint64 value) {
                    if (value == 1) {
                        log info, 3: \"Writing Field_D\";
                    }
                }
            }
            method is_even(int value) -> (uint32) {
                if (value % 2 == 0) {
                    return true;
                } else
                    return false;
            }
        }
    }
}
";
#[test]
fn in3_full_bank_correct_indent() {
    let rules = set_up();
    assert_indentation(IN3_FULL_BANK_CORRECT_INDENT, 0, rules);
}

pub static IN3_STRUCTS_BAD_INDENT: &str = "
typedef struct {
     uint16 idx;
       uint16 qid_co;
} hqm_cq_list_release_ctx_t;

typedef layout \"little-endian\" {
     bitfields 8 {
        uint2 rsvd             @ [7:6];
        uint1 error_f          @ [5:5];
        uint1 int_arm          @ [4:4];
        uint1 qe_valid         @ [3:3];
        uint1 qe_frag          @ [2:2];
        uint1 qe_comp          @ [1:1];
        uint1 cq_token         @ [0:0];
    } byte;
} prod_qe_cmd_t;
";
#[test]
fn in3_structs_bad_indent() {
    let rules = set_up();
    assert_indentation(IN3_STRUCTS_BAD_INDENT, 3, rules);
}

pub static IN3_COND_STRUCTURE_BAD_INDENT: &str = "
method control_device() {
    if (control.start == 1) {
    log info, 2: 'Starting the device';
            status.enabled = 1;
    } else if (control.stop == 1) {
                log info, 2: 'Stopping the device';
        status.enabled = 0;
    } else {
    log info, 2: 'No control action taken';
    }
}
";
#[test]
fn in3_cond_structure_bad_indent() {
    let rules = set_up();
    assert_indentation(IN3_COND_STRUCTURE_BAD_INDENT, 4, rules);
}

pub static IN9_CORRECT_CASE_INDENT: &str = "
method some_switch(int arg) {
    switch(arg) {
    case ZERO:
#if (asdd == 0) {
        some_call();
}
        if (a) {
            return;
        }
        some_call();
        break;
    default: { return; }
    }
}
";

pub static IN9_INCORRECT_CASE_INDENT: &str = "
method some_switch(int arg) {
    switch(arg) {
      case ZERO:
#if (asdd == 0) {
          some_call();
}
          if (a) {
            return;
        }
        some_call();
        break;
    case ONE: {
          return;
    }
    default: { return; }
    }
}
";

#[test]
// #[ignore]
fn in9_correct_case_indent() {
    let rules = set_up();
    assert_snippet(IN9_CORRECT_CASE_INDENT, 0, &rules);
    assert_snippet(IN9_INCORRECT_CASE_INDENT, 4, &rules);
}

pub static IN6_CONTINUATION_LINE_INCORRECT: &str = "
method set_irq() {
    interrupt_enabled =
irq_enabled(interrupt_device);
}
";

pub static IN6_CONTINUATION_LINE_INCORRECT_2: &str = "
bank regs {
    register control size 4 @ 0x00 {
        field enable @ [0];
        field mode @ [2:1];
        field status @ [31:3] {
            param init_val = (1 << 2) |
                                   (1 << 1);
        }
    }
}
";

pub static IN6_CONTINUATION_LINE_INCORRECT_3: &str = "
method write(uint64 value) {
    local uint64 a = value;
    local uint64 result = a <<
                               2;
    log info: 'Writing to register, result after left shift = %x', result;
}
";

pub static IN6_CONTINUATION_LINE_OK: &str = "
method set_irq() {
    interrupt_enabled =
        irq_enabled(interrupt_device);
}
";

pub static IN6_CONTINUATION_LINE_OK_2: &str = "
method calculate_sum(uint64 a, uint64 b) -> (uint64) {
    return (a + b) * (a - b) +
        (a * b);
}
";

pub static IN6_CONTINUATION_LINE_OK_3: &str = "
bank regs {
    register example_register size 4 @ 0x00 {
        method read() -> (uint64) {
            local uint64 value = (this.val + 10) *
                (this.val - 5);
            return value;
        }
    }
}
";

#[test]
fn in6_continuation_line() {
    let rules = set_up();

    assert_snippet(IN6_CONTINUATION_LINE_INCORRECT, 1, &rules);
    assert_snippet(IN6_CONTINUATION_LINE_INCORRECT_2, 1, &rules);
    assert_snippet(IN6_CONTINUATION_LINE_INCORRECT_3, 1, &rules);
    assert_snippet(IN6_CONTINUATION_LINE_OK, 0, &rules);
    assert_snippet(IN6_CONTINUATION_LINE_OK_2, 0, &rules);
    assert_snippet(IN6_CONTINUATION_LINE_OK_3, 0, &rules);
}

}
