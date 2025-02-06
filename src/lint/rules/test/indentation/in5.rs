use crate::lint::rules::test::common::{set_up};

pub static TEST_01_BASIC: &str = "
call_func(a,b);
";
#[test]
fn test_01_basic() {
    let rules = set_up();
    assert_eq!(1,1);
    // assert_indentation(TEST_01_BASIC, 1, rules);
}
