//! Data structures relating to types

use crate::ast;
use crate::generics::replace_generics;
use crate::infer::TyVarId;
use crate::intern::Arena;
use crate::intern::Int;
use crate::ir::{self, DefId, DefKind, Path};

/// This contains the owned type context.
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

/// The type context is an internment arena for all types
#[derive(Debug, Clone, Copy)]
pub struct TyCtx<'ty>(&'ty TyCtxS<'ty>);

#[derive(Debug)]
struct TyCtxS<'ty> {
    pub ty_arena: Arena<TyKind<'ty>>,
}

impl<'ty> TyCtx<'ty> {
    /// Intern a type kind and get its Ty
    pub fn int(self, ty: TyKind<'ty>) -> Ty<'ty> {
        Ty(self.0.ty_arena.int(ty))
    }
}

/// Create a new range type with usize
pub fn range_ty(ctx: TyCtx<'_>) -> Ty<'_> {
    ctx.int(TyKind::Range(
        ctx.int(TyKind::Primitive(PrimitiveType::USize)),
    ))
}

/// Create a new primitive type
pub fn primitive_ty(ctx: TyCtx<'_>, pt: PrimitiveType) -> Ty<'_> {
    ctx.int(TyKind::Primitive(pt))
}

/// Create a void type
pub fn void_ty(ctx: TyCtx<'_>) -> Ty<'_> {
    primitive_ty(ctx, PrimitiveType::Void)
}

/// Create a bool type
pub fn bool_ty(ctx: TyCtx<'_>) -> Ty<'_> {
    primitive_ty(ctx, PrimitiveType::Bool)
}

/// Create an error type
pub fn err_ty(ctx: TyCtx<'_>) -> Ty<'_> {
    ctx.int(TyKind::Err)
}

/// This represents all primitive types
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

    // Pointer size unsigned integer
    USize,

    // Unsigned integers
    U64,
    U32,
    U16,
    U8,

    /// Integer represents an integer with unknown size and sign
    Integer,
}

impl PrimitiveType {
    /// Returns true if the primitive type is either a float or an integer
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

    /// Returns true if the primitive type is a float
    pub fn is_float(&self) -> bool {
        matches!(self, PrimitiveType::F32 | PrimitiveType::F64)
    }

    /// Returns true if the primitive type is an integer of any size or sign
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

/// The type of a pointer
#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub enum PointerType {
    /// Mutable pointer
    StarMut,
    /// Immutable pointer (currently treated as mutable)
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

/// A type that is stored in the internment arena
#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub struct Ty<'ty>(pub Int<'ty, TyKind<'ty>>);

/// Semantic type values
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum TyKind<'ty> {
    /// Primitive types such as integers and floats
    Primitive(PrimitiveType),

    /// A placeholder for a type parameter
    Param(String),

    /// A pointer type with the given mutability and inner type
    Pointer(PointerType, Ty<'ty>),

    /// A tuple type
    Tuple(Vec<Ty<'ty>>),

    /// A function type. This represents a function pointer with the given
    /// parameters and return type.
    Fun(Vec<Ty<'ty>>, Ty<'ty>),

    /// A sized array. It has a static size and inner type.
    SizedArray(usize, Ty<'ty>),

    /// An unsized array. This is only used with a pointer to make a slice.
    UnsizedArray(Ty<'ty>),

    /// A range type (`0..20`). For now the type should always be `usize`
    Range(Ty<'ty>),

    /// An abstract datatype such as a struct or enum
    Adt(AdtType<'ty>),

    /// A type variable which hasn't yet been resolved.  See [`infer`].
    TyVar(TyVarId),

    /// A placeholder for types that are unknown due to a compile time error.
    Err,
}

/// An abstract datatype such as a struct or enum.  This contains the [`DefId`]
/// of the data type it references along with any type parameters.  The [`Path`]
/// field is used for debugging.
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct AdtType<'ty> {
    /// The [`DefId`] for the referenced datatype.
    pub def_id: DefId,

    /// The [`Path`] for the referenced datatype (corresponds with `def_id`).
    pub path: Path,

    /// Any type parameters for this abstract type. These are mapped to the
    /// type params in the adt definition and used to resolve real types.
    /// For example, an `AdtType` with `ty_params` of `[i32, u64]` referring to
    /// a struct definition with signature `struct<T, U> {a: T, b: U}` will
    /// replace the values of `T` and `U` with `i32` and `u64` respectively.
    pub ty_params: Vec<Ty<'ty>>,
}

impl<'ty> AdtType<'ty> {
    /// Gets a the type of a field from an abstract datatype with all type
    /// parameters replaced.  This function returns `Some` when the field exists
    /// or `None` when it doesn't exist.  If this is called on an ADT referencing
    /// an enum or function, it will panic.
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

    /// Gets a the type of a method from an abstract datatype with all type
    /// parameters replaced.  This function returns `Some` when the method exists
    /// or `None` when it doesn't exist.  If this is called on an ADT referencing
    /// an function, it will panic.
    pub fn get_method_ty(&self, md: &ir::Module<'ty>, method: &str) -> Option<Ty<'ty>> {
        match md.get_def_by_id(self.def_id).kind() {
            DefKind::Enum {
                ty_params: _,
                symbols,
                ..
            }
            | DefKind::Struct {
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
            def => panic!("{:?}", def),
        }
    }

    /// Gets a the type and def_id of a method from an abstract datatype with all type
    /// parameters replaced.  This function returns `Some` when the method exists
    /// or `None` when it doesn't exist.  If this is called on an ADT referencing
    /// an function, it will panic.
    pub fn get_method_ty_and_def_id(
        &self,
        md: &ir::Module<'ty>,
        method: &str,
    ) -> Option<(Ty<'ty>, Vec<Ty<'ty>>, DefId)> {
        match md.get_def_by_id(self.def_id).kind() {
            DefKind::Enum {
                ty_params: _,
                symbols,
                ..
            }
            | DefKind::Struct {
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
    /// Returns true if this type is a subtype of or equal to the given type.  This currently
    /// only applies to integer types and void pointers.
    ///
    /// ```text
    /// forall T . (*T) `subtype_of` (*void)
    /// forall T . (*void) `subtype_of` (*T)
    /// ```
    pub fn subtype_of(self, other: Ty<'ty>) -> bool {
        match (self.kind(), other.kind()) {
            (TyKind::Primitive(lpt), TyKind::Primitive(rpt)) => lpt < rpt,
            (
                TyKind::Pointer(_, _),
                TyKind::Pointer(_, Ty(Int(TyKind::Primitive(PrimitiveType::Void)))),
            )
            | (
                TyKind::Pointer(_, Ty(Int(TyKind::Primitive(PrimitiveType::Void)))),
                TyKind::Pointer(_, _),
            ) => true,
            _ => self == other,
        }
    }

    /// Get the type kind contained in this `Ty`
    pub fn kind(self) -> &'ty TyKind<'ty> {
        self.0 .0
    }

    /// Fully dereference a type by converting pointers to their inner values.
    /// For example, `****T` becomes `T`.
    pub fn full_deref_ty(mut self) -> Ty<'ty> {
        while let TyKind::Pointer(_, ty) = self.0 .0 {
            self = *ty
        }
        self
    }

    /// Dereference a type once.  Returns `None` if the type is not a pointer.
    /// For example, `**T` becomes `*T`.
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

    /// True if this type is an integer primitive with unknown size and sign
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
