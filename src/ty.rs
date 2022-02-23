use crate::ast;
use crate::symbol::Name;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub enum PrimitiveType {
    Void,
    Bool,

    F64,
    F32,

    I64,
    I32,
    I16,
    I8,

    USize,

    U64,
    U32,
    U16,
    U8,

    Integer,
}

impl PrimitiveType {
    pub fn is_numeric(&self) -> bool {
        match self {
            PrimitiveType::I8
            | PrimitiveType::I16
            | PrimitiveType::I32
            | PrimitiveType::I64
            | PrimitiveType::U8
            | PrimitiveType::U16
            | PrimitiveType::U32
            | PrimitiveType::U64
            | PrimitiveType::USize
            | PrimitiveType::Integer
            | PrimitiveType::F32
            | PrimitiveType::F64 => true,
            _ => false,
        }
    }
    pub fn is_float(&self) -> bool {
        match self {
            PrimitiveType::F32 | PrimitiveType::F64 => true,
            _ => false,
        }
    }
    pub fn is_integral(&self) -> bool {
        match self {
            PrimitiveType::I8
            | PrimitiveType::I16
            | PrimitiveType::I32
            | PrimitiveType::I64
            | PrimitiveType::U8
            | PrimitiveType::U16
            | PrimitiveType::U32
            | PrimitiveType::U64
            | PrimitiveType::USize
            | PrimitiveType::Integer => true,
            _ => false,
        }
    }
}

impl From<&ast::PrimitiveType> for PrimitiveType {
    fn from(ty: &ast::PrimitiveType) -> Self {
        match ty {
            ast::PrimitiveType::I8 => PrimitiveType::I8,
            ast::PrimitiveType::I16 => PrimitiveType::I16,
            ast::PrimitiveType::I32 => PrimitiveType::I32,
            ast::PrimitiveType::I64 => PrimitiveType::I64,
            ast::PrimitiveType::U8 => PrimitiveType::U8,
            ast::PrimitiveType::U16 => PrimitiveType::U16,
            ast::PrimitiveType::U32 => PrimitiveType::U32,
            ast::PrimitiveType::U64 => PrimitiveType::U64,
            ast::PrimitiveType::USize => PrimitiveType::USize,
            ast::PrimitiveType::F32 => PrimitiveType::F32,
            ast::PrimitiveType::F64 => PrimitiveType::F64,
            ast::PrimitiveType::Bool => PrimitiveType::Bool,
            ast::PrimitiveType::Void => PrimitiveType::Void,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum PointerType {
    StarMut,
    Star,
}

impl From<&ast::PointerType> for PointerType {
    fn from(ty: &ast::PointerType) -> Self {
        match ty {
            ast::PointerType::StarMut => PointerType::StarMut,
            ast::PointerType::Star => PointerType::Star,
        }
    }
}

/// Semantic type values
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Primitive(PrimitiveType),
    Param(String),
    Pointer(PointerType, Box<Type>),
    Tuple(Vec<Type>),
    Fun(Vec<Type>, Box<Type>),
    SizedArray(usize, Box<Type>),
    UnsizedArray(Box<Type>),
    Range(Box<Type>),
    Lhs(Box<Type>),
    Struct {
        name: Name,
        params: Vec<Type>,
        members: HashMap<String, Type>,
    },
    Err,
    Unknown,
}

impl Type {
    pub fn ptr(&self) -> Type {
        Type::Pointer(PointerType::Star, Box::new(self.clone()))
    }

    pub fn mut_ptr(&self) -> Type {
        Type::Pointer(PointerType::StarMut, Box::new(self.clone()))
    }

    pub fn is_numeric(&self) -> bool {
        match self {
            Type::Primitive(x) => x.is_numeric(),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_primitive_ord() {
        use super::PrimitiveType::*;
        assert!(Void < Bool);
        assert!(Integer > USize);
    }
}
