# Supported Rules

Below are listed the currently supported rules for linting:

## Spacing
- **SP.braces**: spaces around braces (`{` and `}`)
- **SP.punct**: spaces after but not before colon, semicolon and comma
- **NSP.funpar**: no spaces between a function/method name and its opening parenthesis
- **NSP.inparen**: no spaces immediately inside parentheses or brackets
- **NSP.unary**: no spaces between a unary operator and its operand
- **NSP.TrailingWhitespace**: no spaces between the last token in a line and the corresponding newline `\n`

## Line Length
- **LL1**: Lines should be kept shorter than 80 characters. Longer lines wrap or become partially invisible in editors whose windows have the standard width of 80 columns, which makes the code much harder to read

# Work in progress

## Indentation
- **IN1**: Lines are indented four spaces for each indentation level
- **IN2**: Tab characters (ASCII 9) should never be used to indent lines
- **IN3**: If the previous line contains an opening brace without corresponding closing brace, the current line should be indented one level more than the previous line
- **IN4**: An closing brace at the beginning of a line is indented one level less than the previous line. A closing brace should only ever appear on the same line as the opening brace or first on a line
- **IN5**: A continuation line that is broken inside a parenthesized expression is indented to line up inside the corresponding parenthesis on the previous line
- **IN6**: A continuation line not broken inside a parenthesized expression is indented one level
- **IN7**: Any line not indented according to the rules above is indented to same level as the preceding non-empty line
- **IN9**: Case labels are indented one level less than surrounding lines, so that they are on the same level as the switch statement. The same applies to goto labels, but keep an indentation of at least one space, to avoid mistaking them for top-level definitions
- **IN10**: When the body of a while or for loop is left empty, indent the semicolon to the appropriate statement level

# Pending Rules

## Spacing
- **SP.reserved**: spaces around reserved words, such as `if`, `else`, `default`, `size`, `const` and `in`, except when a reserved word is used as an identifier (e.g., `local uint8 *data;`)
- **SP.binop**: spaces around binary operators except the dereferencing operators dot (`a.b`) and arrow (`a->b`)
- **SP.ternary**: spaces around `?` and `:` in the ternary `?:` operator
- **SP.ptrdecl**: space between a type and the `*` marking a pointer
- **SP.comment**: spaces around the comment delimiters `//`, `/*` and `**/`
- **NSP.ptrdecl**: no space after the `*` marking a pointer in a declaration

## Braces
- **BR1**: No braces are required around single-statement blocks (but see the rule for comments)
- **BR2**: Empty DML object declarations should be written with a semicolon instead of an empty brace pair
- **BR3**: Methods should have the opening brace on the same line as the method declaration

## Parentheses
- **PA1**: Parentheses not required by the language may be added to expressions for clarity or indentation
- **PA2**: Parentheses should be added when the operator precedence is not intuitively obvious. This is mandatory to resolve precedence between the following operators, even if it is well-defined by the language:
    ```
    1. || vs &&
    2. bitwise operators (|, &, ^) vs each other
    3. bitwise operators vs arithmetic operators (+, -, *, /, %)
    4. bitwise operators vs comparisons (==, !=, >, <, >=, <=)
    5. shift operators (<<, >>) vs arithmetic operators
    6. comparisons vs each other
    7. shift operators vs each other
    ```
- **PA3**: When neither language nor understanding or layout require parentheses, they should be omitted
- **PA4**: Parentheses should also be added to assignment statements inside expressions, to clearly show that they were intended

## Line Length
- **LL2**: Break long lines before binary operators, not after
- **LL3**: Break conditional expressions before the `?`, or both before the `?` and before the `:`
- **LL4**: Following lines should be indented at their natural position. Add parentheses if it makes indenting easier. May also add spaces in expressions to make them line up
- **LL5**: Break long method declarations with output parameters before the arrow
- **LL6**: Function and method invocations can be broken after the opening parenthesis, with the continuation lines indented one level

## Naming
#### General
- **NN1** In absence of other rules, identifiers are written in lower case letters, words separated by underscores
- **NN2** Do not append a number as a general method to create new identifiers, other than in very special circumstances

#### Method names
- **NM1** Methods that are executed primarily for their side-effect should be named after what they do. Methods executed for their return value should be named after what they return. If the method is a predicate (returning a boolean value), it should be named after the condition when it returns a true value

#### Variable and object names
- **NV1** Variables should be named after what they contain, not from the variable or its type. The more local a variable is, the shorter can be its name. Use long, descriptive names for top-level names; use short names in local scopes. Names more frequently used can also be shorter
- **NV2** In particular, do not use tmp or ptr in identifiers; it is rare that it is needed to point out that a variable contains a temporary value or a pointer
- **NV3** Do not prefix names with an article, such as `an_object` or `the_score`

#### Type names
- **NT1** Typedef names should end in `_t`. Typedef structs unless only used locally