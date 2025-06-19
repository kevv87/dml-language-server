use crate::lint::rules::tests::common::{set_up, assert_snippet};
use crate::lint::rules::RuleType;

static SP_RESERVED_IF_INCORRECT: &str = "
method this_is_some_method(bool flag) {
    local int this_some_integer = 0x666;
    if(this_some_integer == 0x666)
        return;

    if(this_some_integer == 0x667) {
        if(flag) {
            some_cal();
        } else {
            return;
        }
    }
}
";
#[test]
fn sp_reserved_incorrect() {
    let mut rules = set_up();
    let expected_errors = define_expected_errors!(
        RuleType::SpReserved,
        (3, 3, 4, 7),
        (6, 6, 4, 7),
        (7, 7, 8, 11),
    );
    assert_snippet(SP_RESERVED_IF_INCORRECT, expected_errors, &rules);
    // Test rule disable
    rules.sp_reserved.enabled = false;
    assert_snippet(SP_RESERVED_IF_INCORRECT, vec![], &rules);
}

static SP_RESERVED_IF_CORRECT: &str = "
method this_is_some_method(bool flag) {
    local int this_some_integer = 0x666;
    if (this_some_integer == 0x666)
        return;

    if (this_some_integer == 0x667) {
        if (flag) {
            some_cal();
        } else {
            return;
        }
    }
}
";
#[test]
fn sp_reserved_correct() {
    let rules = set_up();
    assert_snippet(SP_RESERVED_IF_CORRECT, vec![], &rules);
}