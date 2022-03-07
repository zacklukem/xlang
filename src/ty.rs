//! Data structures relating to types

use crate::ast;
use crate::generics::replace_generics;
use crate::infer::TyVarId;
use crate::intern::Arena;
use crate::intern::Int;
use crate::ir::{self, DefId, DefKind, Path};

pub struct TyCtxContainer<'ty> {
    ctx: TyCtxS<'ty>,
}

impl<'ty> Default for TyCtxContainer<'ty> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'ty> TyCtxContainer<'ty> {
    pub fn new() -> TyCtxContainer<'ty> {
        Self {
            ctx: TyCtxS {
                ty_arena: Arena::new(),
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
    pub ty_arena: Arena<TyKind<'ty>>,
}

impl<'ty> TyCtx<'ty> {
    /// Intern a type and get its Ty
    pub fn int(self, ty: TyKind<'ty>) -> Ty<'ty> {
        Ty(self.0.ty_arena.int(ty))
    }
}

pub fn range_ty(ctx: TyCtx<'_>) -> Ty<'_> {
    ctx.int(TyKind::Range(
        ctx.int(TyKind::Primitive(PrimitiveType::USize)),
    ))
}

pub fn primitive_ty(ctx: TyCtx<'_>, pt: PrimitiveType) -> Ty<'_> {
    ctx.int(TyKind::Primitive(pt))
}

pub fn void_ty(ctx: TyCtx<'_>) -> Ty<'_> {
    primitive_ty(ctx, PrimitiveType::Void)
}

pub fn bool_ty(ctx: TyCtx<'_>) -> Ty<'_> {
    primitive_ty(ctx, PrimitiveType::Bool)
}

pub fn err_ty(ctx: TyCtx<'_>) -> Ty<'_> {
    ctx.int(TyKind::Err)
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
        matches!(
            self,
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
                | PrimitiveType::F64
        )
    }
    pub fn is_float(&self) -> bool {
        matches!(self, PrimitiveType::F32 | PrimitiveType::F64)
    }
    pub fn is_integral(&self) -> bool {
        matches!(
            self,
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
        )
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

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
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
    Adt(AdtType<'ty>),
    TyVar(TyVarId),
    Err,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct AdtType<'ty> {
    pub def_id: DefId,
    pub path: Path,
    pub ty_params: Vec<Ty<'ty>>,
}

impl<'ty> AdtType<'ty> {
    pub fn get_field(&self, md: &ir::Module<'ty>, field: &str) -> Option<Ty<'ty>> {
        match md.get_def_by_id(self.def_id).kind() {
            DefKind::Struct {
                ty_params: ty_param_names,
                members,
                ..
            } => {
                let ty = *members.get(field)?;
                let generics = ty_param_names
                    .iter()
                    .cloned()
                    .zip(self.ty_params.iter().copied())
                    .collect::<Vec<_>>();
                let ty = replace_generics(md.ty_ctx(), ty, &generics);
                Some(ty)
            }
            _ => panic!(),
        }
    }

    pub fn get_method_ty(&self, md: &ir::Module<'ty>, method: &str) -> Option<Ty<'ty>> {
        match md.get_def_by_id(self.def_id).kind() {
            DefKind::Struct {
                ty_params: _,
                symbols,
                ..
            } => {
                let def_id = *symbols.get(method)?;
                let ty = md
                    .get_def_by_id(def_id)
                    .fn_type(md.ty_ctx(), &self.ty_params)
                    .unwrap();
                Some(ty)
            }
            _ => panic!(),
        }
    }

    pub fn get_method_ty_and_def_id(
        &self,
        md: &ir::Module<'ty>,
        method: &str,
    ) -> Option<(Ty<'ty>, Vec<Ty<'ty>>, DefId)> {
        match md.get_def_by_id(self.def_id).kind() {
            DefKind::Struct {
                ty_params: _,
                symbols,
                ..
            } => {
                let def_id = *symbols.get(method)?;
                let ty = md
                    .get_def_by_id(def_id)
                    .fn_type(md.ty_ctx(), &self.ty_params)
                    .unwrap();
                Some((ty, self.ty_params.clone(), def_id))
            }
            _ => panic!(),
        }
    }
}

impl<'ty> Ty<'ty> {
    pub fn full_deref_ty(mut self) -> Ty<'ty> {
        while let TyKind::Pointer(_, ty) = self.0 .0 {
            self = *ty
        }
        self
    }

    pub fn deref_ty(self) -> Option<Ty<'ty>> {
        if let TyKind::Pointer(_, ty) = self.0 .0 {
            Some(*ty)
        } else {
            None
        }
    }

    /// Get the ref level of a type, i.e. the number of references:
    ///
    /// |Type    |Level|
    /// |--------|-----|
    /// | `i8`   | 0   |
    /// | `*i8`  | 1   |
    /// | `**i8` | 2   |
    /// | ...          |
    ///
    pub fn ref_level(self) -> u8 {
        if let TyKind::Pointer(_, ty) = self.0 .0 {
            ty.ref_level() + 1
        } else {
            0
        }
    }

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
        matches!(self.0 .0, TyKind::Primitive(x) if x.is_numeric())
    }

    pub fn is_integer_ukn(self) -> bool {
        matches!(self.0 .0, TyKind::Primitive(PrimitiveType::Integer))
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
