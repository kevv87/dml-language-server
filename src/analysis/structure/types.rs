//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT
use crate::analysis::parsing::{misc, types};
use crate::analysis::parsing::tree::{ZeroSpan, TreeElement};
use crate::analysis::LocalDMLError;
use crate::analysis::structure::expressions::DMLString;
use crate::analysis::FileSpec;

// TODO/NOTE: Currently we use the range of the declaration in source
// as a placeholder for the actual type AST
pub type DMLType = ZeroSpan;

pub fn deconstruct_typedecl<'a>(
    content: &misc::TypeDeclContent,
    _report: &mut Vec<LocalDMLError>,
    file: FileSpec<'a>) -> (Option<DMLString>, Option<DMLType>) {
    // TODO: Correctly combine info from cdecl with this to construct actual
    // type. Currently we just faux the type location as the entire typedecl
    match content {
        misc::TypeDeclContent::Ident(tok) =>
            (DMLString::from_token(tok, file),
             Some(ZeroSpan::from_range(content.range(), file.path))),
        misc::TypeDeclContent::Array(inner_decl, _, _, _) =>
            match &inner_decl.content {
                Some(inner_decl_obj) => {
                    // TODO: array the type
                    inner_decl_obj.with_content(
                        |con|deconstruct_typedecl(con, _report, file),
                    (None, None))
                },
                None => (None, Some(ZeroSpan::from_range(content.range(),
                                                         file.path))),
            },
        misc::TypeDeclContent::Fun(inner_decl, _, _, _, _) =>
            match &inner_decl.content {
                Some(inner_decl_obj) => {
                    // TODO: convert to actual function type
                    inner_decl_obj.with_content(
                        |con|deconstruct_typedecl(con, _report, file),
                    (None, None))
                },
                None => (None, Some(
                    ZeroSpan::from_range(content.range(),
                                         file.path))),
            },
        misc::TypeDeclContent::Parens(_, _, inner_decl, _) =>
            match &inner_decl.content {
                Some(inner_decl_obj) => {
                    // TODO: modify with in-parens modifiers
                    inner_decl_obj.with_content(
                        |con|deconstruct_typedecl(con, _report, file),
                    (None, None))
                },
                None => (None, Some(ZeroSpan::from_range(content.range(),
                                                         file.path))),
            },
    }
}

// TODO: For now this does not need to obtain the actual type, only the name
// of the declaration
pub fn deconstruct_cdecl<'a>(content: &misc::CDeclContent,
                             report: &mut Vec<LocalDMLError>,
                             file: FileSpec<'a>) ->
    (Option<DMLString>, Option<DMLType>) {
    // let is_const = content.consttok.is_some();
    // let base = TODO;
    // let modififiers = TODO;
    match &content.decl.content {
        Some(typedeclobj) => {
            // I _think_ a typedecl can never be an empty object, (since an
            // empty typedecl will just become None)
            typedeclobj.with_content(
                |con|deconstruct_typedecl(con, report, file),
                (None, None))
        },
        None => (None, Some(ZeroSpan::from_range(content.base.range(),
                                                 file.path))),
    }
}

#[allow(clippy::ptr_arg)]
pub fn to_type<'a>(content: &types::CTypeDecl,
                   _report: &mut Vec<LocalDMLError>,
                   file: FileSpec<'a>) -> Option<DMLType> {
    content.with_content(|con|Some(ZeroSpan::from_range(con.range(),
                                                        file.path)),
                         None)
}
