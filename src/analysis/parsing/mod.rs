//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT
// Load parser and tree first to ensure existance of macros
#[macro_use]
pub mod parser;
#[macro_use]
pub mod tree;
pub mod expression;
pub mod misc;
pub mod statement;
pub mod structure;
pub mod lexer;
pub mod types;

pub use structure::{DMLObject, parse_toplevel, post_parse_toplevel};
