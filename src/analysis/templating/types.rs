//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT
use crate::analysis::parsing::tree::ZeroSpan;


use crate::analysis::structure::types::DMLType;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DMLBaseType {
    no_info: ZeroSpan,
}

impl DMLBaseType {
    pub fn span(&self) -> &ZeroSpan {
        &self.no_info
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DMLStructType {
    no_info: ZeroSpan,
}

impl DMLStructType {
    pub fn span(&self) -> &ZeroSpan {
        &self.no_info
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DMLConcreteType {
    BaseType(DMLBaseType),
    StructType(DMLStructType),
}

impl DMLConcreteType {
    pub fn span(&self) -> &ZeroSpan {
        match self {
            DMLConcreteType::BaseType(b) => b.span(),
            DMLConcreteType::StructType(s) => s.span(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DMLResolvedType {
    Actual(DMLConcreteType),
    // In some cases, a type fails to resolve but we do not want to drop
    // the thing that depends on it, in this case we provide the dummy variant
    Dummy(ZeroSpan),
}

impl DMLResolvedType {
    pub fn span(&self) -> &ZeroSpan {
        match self {
            DMLResolvedType::Actual(typ) => typ.span(),
            DMLResolvedType::Dummy(span) => span,
        }
    }

    pub fn is_dummy(&self) -> bool {
        matches!(self, DMLResolvedType::Dummy(_))
    }

    pub fn equivalent(&self, _: &DMLResolvedType) -> bool {
        // TODO: actual type comparison beyond this
        // Currently, we are using this only to typecheck arguments
        // for method overrides, so returning true avoids
        // false negatives
        true
    }
}

impl From<DMLConcreteType> for DMLResolvedType {
    fn from(frm: DMLConcreteType) -> DMLResolvedType {
        DMLResolvedType::Actual(frm)
    }
}

pub fn eval_type(ast: &DMLType, _location: (), _scope: (),
                 _in_extern: bool, _typename_hint: Option<&str>,
                 _allow_void: bool)
                 -> (Vec<DMLStructType>, DMLConcreteType) {
    (vec![], DMLConcreteType::BaseType(DMLBaseType {
        // TODO: replace with .span once types are concrete
        no_info: *ast }))
}

pub fn eval_type_simple(ast: &DMLType, location: (), scope: ())
    -> (Vec<DMLStructType>, DMLConcreteType) {
    eval_type(ast, location, scope, false, None, false)
}
