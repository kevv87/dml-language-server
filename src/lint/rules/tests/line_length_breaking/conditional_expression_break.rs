use crate::lint::rules::tests::common::{set_up, robust_assert_snippet as assert_snippet};
use crate::lint::rules::RuleType;


static CORRECT_BREAK_AFTER_QUESTION: &str = "
method bootprep_type_to_string(uint8 prep_type) -> (const char*) {
    return
        prep_type == PREP_GENERAL ? \"PrepGeneral\":
            \"PrepEarly\";
}";
#[test]
fn condexpr_correct_break_after_colon() {
    let rules = set_up();
    let expected_errors = vec![];
    assert_snippet(CORRECT_BREAK_AFTER_QUESTION, expected_errors, &rules);
}

static CORRECT_BREAK_AFTER_COLON_AND_QUESTION: &str = "
method bootprep_type_to_string(uint8 prep_type) -> (const char*) {
    return
        prep_type == PREP_GENERAL
            ? \"PrepGeneral\"
                : \"PrepEarly\";
}";
#[test]
fn condexpr_correct_break_after_colon_and_() {
    let rules = set_up();
    let expected_errors = vec![];
    assert_snippet(CORRECT_BREAK_AFTER_COLON_AND_QUESTION, expected_errors, &rules);
}

static BREAK_ONLY_AFTER_COLON: &str = "
harvest_resource(my->gas < GAS_THRESHOLD
                 ? Rsrc_Gas
                 : (my->minerals < MINERAL_THRESHOLD
                    ? Rsrc_Minerals : nearest_resource()));
";
#[test]
fn condexpr_broken_after_paren_break_only_after_colon() {
    let rules = set_up();
    let expected_errors = vec![];
    assert_snippet(BREAK_ONLY_AFTER_COLON, expected_errors, &rules);
}

static SNIPPET_TEST: &str = "
method bootprep_type_to_string(uint8 prep_type) -> (const char*) {
    return
        prep_type == PREP_GENERAL ?
            \"PrepGeneral\" :
                prep_type == PREP_EARLY ? \"PrepEarly\" :
                    \"UnknownBootPrepType\";
}";
#[test]
fn condexpr_broken_after_question() {
    let rules = set_up();
    let expected_errors = define_expected_errors!(
        RuleType::LL3,
        (4, 5, 8, 67),
        (5, 5, 48, 69),
    );
    assert_snippet(SNIPPET_TEST, expected_errors, &rules);
}

