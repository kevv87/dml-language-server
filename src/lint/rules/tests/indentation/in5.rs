use crate::lint::rules::tests::common::{set_up, assert_snippet};

// A continuation line that is broken inside a parenthesized expression 
// is indented to line up inside the corresponding parenthesis on the previous line

pub static IN5_OPERATION_PAREN_OK: &str = "
param result = (((reg0.val * reg1.enable.val)
                 & mask_reg)
                + 1);
";
pub static IN5_OPERATION_PAREN_ERR: &str = "
param result = (((reg0.val * reg1.enable.val)
                & mask_reg)
                 + 1);
";

pub static IN5_METHODARGS_PAREN_OK: &str = "
method some_method(int a,
                   int b, bool c) {
    return c ? a + b : a - b;
}
";
pub static IN5_METHODARGS_PAREN_ERR: &str = "
method some_method(int a,
    int b, bool c) {
    return c ? a + b : a - b;
}
";

pub static IN5_FUNCALL_PAREN_OK: &str = "
method effect() {
    callback(0xABC,
             identifier,
             false);
}
";
pub static IN5_FUNCALL_PAREN_ERR: &str = "
method effect() {
    callback(0xABC,
        identifier,
        false);
}
";

pub static IN5_IF_PAREN_OK: &str = "
method callback() {
    if (conditionX &&
        conditionY) {
        return;
    }
}
";
pub static IN5_IF_PAREN_ERR: &str = "
method callback() {
    if (conditionX &&
          conditionY) {
        return;
    }
}
";

pub static IN5_WHILE_PAREN_OK: &str = "
method callback() {
    while (conditionX 
           || conditionY) {
        update_conditions();
    }
}
";
pub static IN5_WHILE_PAREN_ERR: &str = "
method callback() {
    while (initial
        + offset 
           <= size) {
        offset++;
    }
}
";

pub static IN5_DO_WHILE_PAREN_OK: &str = "
method callback() {
    do {
        log info: 'some message';
    } while (conditionX 
             || conditionY);
}
";
pub static IN5_DO_WHILE_PAREN_ERR: &str = "
method callback() {
    do {
        set_values();
    } while (conditionX 
            || conditionY);
}
";

pub static IN5_FOR_PAREN_OK: &str = "
method callback() {
    for (int i = 0;
         i < 10;
         i++) {
        log info: 'some message';
    }
}
";
pub static IN5_FOR_PAREN_ERR: &str = "
method callback() {
    for (int i = 0;
           i < 10;
             i++) {
        log info: 'some message';
    }
}
";

pub static IN5_FOREACH_PAREN_OK: &str = "
method handle() {
    #foreach item in (reg0,
            reg1,
                reg2,
                    reg3) {
        item.update();
    }
}
";
pub static IN5_FOREACH_PAREN_ERR: &str = "
method handle() {
    #foreach item in (reg0, reg1
        reg2, reg3) {
        item.update();
    }
}
";

pub static IN5_SWITCH_PAREN_OK: &str = "
method select_from_result() {
    switch (a 
            + b
            - c) {
    case 0:
        log info: 'Result is zero';
        break;
    case 1:
        log info: 'Result is one';
        break;
    default:
        log info: 'Unknown result';
    }
}
";
pub static IN5_SWITCH_PAREN_ERR: &str = "
method select_from_result() {
    switch (a 
              + b
                - c) {
    case 0:
        log info: 'Result is zero';
        break;
    case 1:
        log info: 'Result is one';
        break;
    default:
        log info: 'Unknown result';
    }
}
";

#[test]
fn in5_lineup_inside_parenthesized_expressions() {
    let rules = set_up();

    assert_snippet(IN5_OPERATION_PAREN_OK, 0, &rules);
    assert_snippet(IN5_OPERATION_PAREN_ERR, 1, &rules);

    assert_snippet(IN5_METHODARGS_PAREN_OK, 0, &rules);
    assert_snippet(IN5_METHODARGS_PAREN_ERR, 2, &rules);

    assert_snippet(IN5_FUNCALL_PAREN_OK, 0, &rules);
    assert_snippet(IN5_FUNCALL_PAREN_ERR, 2, &rules);

    assert_snippet(IN5_IF_PAREN_OK, 0, &rules);
    assert_snippet(IN5_IF_PAREN_ERR, 1, &rules);

    assert_snippet(IN5_WHILE_PAREN_OK, 0, &rules);
    assert_snippet(IN5_WHILE_PAREN_ERR, 1, &rules);

    assert_snippet(IN5_DO_WHILE_PAREN_OK, 0, &rules);
    assert_snippet(IN5_DO_WHILE_PAREN_ERR, 1, &rules);

    assert_snippet(IN5_FOR_PAREN_OK, 0, &rules);
    assert_snippet(IN5_FOR_PAREN_ERR, 2, &rules);

    assert_snippet(IN5_FOREACH_PAREN_OK, 0, &rules);
    assert_snippet(IN5_FOREACH_PAREN_ERR, 3, &rules);

    assert_snippet(IN5_SWITCH_PAREN_OK, 0, &rules);
    assert_snippet(IN5_SWITCH_PAREN_ERR, 2, &rules);
}
