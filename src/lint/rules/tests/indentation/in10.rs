use crate::lint::rules::tests::common::{set_up, assert_snippet};

pub static IN10_EMPTY_LOOP_INCORRECT: &str = "
for (s = 0; (1 << s) < x; s++)
;
";

pub static IN10_EMPTY_LOOP_INCORRECT_2: &str = "
for (s = 0; (1 << s) < x; s++)
        ;
";

pub static IN10_EMPTY_LOOP_INCORRECT_3: &str = "
int s = 0;
while ((1 << s) < x)
;
    s++;
";

pub static IN10_EMPTY_LOOP_OK: &str = "
for (s = 0; (1 << s) < x; s++)
    ;
";

pub static IN10_EMPTY_LOOP_OK_2: &str = "
int s = 0;
while ((1 << s) < x)
    ;
    s++;
";

#[test]
fn in10_empty_loop() {
    let rules = set_up();

    assert_snippet(IN10_EMPTY_LOOP_INCORRECT, 1, &rules);
    assert_snippet(IN10_EMPTY_LOOP_INCORRECT_2, 1, &rules);
    assert_snippet(IN10_EMPTY_LOOP_INCORRECT_3, 1, &rules);
    assert_snippet(IN10_EMPTY_LOOP_OK, 0, &rules);
    assert_snippet(IN10_EMPTY_LOOP_OK_2, 0, &rules);
}
