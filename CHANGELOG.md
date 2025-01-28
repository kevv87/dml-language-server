<!--
  © 2024 Intel Corporation
  SPDX-License-Identifier: Apache-2.0 and MIT
-->
# Change Log

## 0.9.6
- Added DFA command-line-option "--suppress-imports" which makes the server not recurse analysis into imported files

## 0.9.5
- Fixed parse error when encountering "default" method calls while parsing switch statements
- Fixed range comparison operation that would occasionally break sorting invariants
