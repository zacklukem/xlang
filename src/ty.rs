//! Data structures relating to types

use crate::ast;
use crate::intern::Arena;
use crate::intern::Int;
use crate::ir::{DefId, Path};

pub struct TyCtxContainer<'ty> {
    ctx: TyCtxS<'ty>,
}

impl<'ty> TyCtxContainer<'ty> {
    pub fn new() -> TyCtxContainer<'ty> {
        Self {
            ctx: TyCtxS {
                arena: Arena::new(),
            },
        }
    }

    pub fn ctx(&'ty self) -> TyCtx<'ty> {
        TyCtx(&self.ctx)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TyCtx<'ty>(&'ty TyCtxS<'ty>);

#[derive(Debug)]
pub struct TyCtxS<'ty> {
    pub arena: Arena<TyKind<'ty>>,
}

impl<'ty> TyCtx<'ty> {
    /// Intern a type and get its Ty
    pub fn int(self, ty: TyKind<'ty>) -> Ty<'ty> {
        Ty(self.0.arena.int(ty))
    }
}

pub fn range_ty<'a>(ctx: TyCtx<'a>) -> Ty<'a> {
    ctx.int(TyKind::Range(
        ctx.int(TyKind::Primitive(PrimitiveType::USize)),
    ))
}

pub fn primitive_ty<'a>(ctx: TyCtx<'a>, pt: PrimitiveType) -> Ty<'a> {
    ctx.int(TyKind::Primitive(pt))
}

pub fn void_ty<'a>(ctx: TyCtx<'a>) -> Ty<'a> {
    primitive_ty(ctx, PrimitiveType::Void)
}

pub fn bool_ty<'a>(ctx: TyCtx<'a>) -> Ty<'a> {
    primitive_ty(ctx, PrimitiveType::Bool)
}

pub fn err_ty<'a>(ctx: TyCtx<'a>) -> Ty<'a> {
    ctx.int(TyKind::Err)
}

pub fn ukn_ty<'a>(ctx: TyCtx<'a>) -> Ty<'a> {
    ctx.int(TyKind::Unknown)
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Hash, Eq)]
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

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
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

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub struct Ty<'ty>(pub Int<'ty, TyKind<'ty>>);

/// Semantic type values
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum TyKind<'ty> {
    Primitive(PrimitiveType),
    Param(String),
    Pointer(PointerType, Ty<'ty>),
    Tuple(Vec<Ty<'ty>>),
    Fun(Vec<Ty<'ty>>, Ty<'ty>),
    SizedArray(usize, Ty<'ty>),
    UnsizedArray(Ty<'ty>),
    Range(Ty<'ty>),
    Lhs(Ty<'ty>),
    Adt(AdtType<'ty>),
    Err,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct AdtType<'ty> {
    pub def_id: DefId,
    pub path: Path,
    pub ty_params: Vec<Ty<'ty>>,
}

impl<'ty> Ty<'ty> {
    /// Make a unsized slice of this type
    pub fn slice_ty(self, ctx: TyCtx<'ty>) -> Ty<'ty> {
        ctx.int(TyKind::UnsizedArray(self))
    }

    /// Make a pointer to this type
    pub fn ptr(self, ctx: TyCtx<'ty>) -> Ty<'ty> {
        ctx.int(TyKind::Pointer(PointerType::Star, self))
    }

    /// Make a mutable pointer to this type
    pub fn mut_ptr(self, ctx: TyCtx<'ty>) -> Ty<'ty> {
        ctx.int(TyKind::Pointer(PointerType::StarMut, self))
    }

    /// True if this type is an integer or floating point type
    pub fn is_numeric(self) -> bool {
        match self.0 .0 {
            TyKind::Primitive(x) => x.is_numeric(),
            _ => false,
        }
    }

    pub fn is_integer_ukn(self) -> bool {
        match self.0 .0 {
            TyKind::Primitive(PrimitiveType::Integer) => true,
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
