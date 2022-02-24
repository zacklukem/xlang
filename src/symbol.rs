use crate::ast;
use crate::const_eval::ConstEvaluator;
use crate::intern::Arena;
use crate::ir_display::type_array_str;
use crate::ty::{self, Ty};
use std::collections::HashMap;

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
    pub arena: Arena<ty::Type<'ty>>,
}

impl<'ty> TyCtx<'ty> {
    /// Intern a type and get its Ty
    pub fn int(self, ty: ty::Type<'ty>) -> Ty<'ty> {
        ty::Ty(self.0.arena.int(ty))
    }
}

/// Represents a name (foo::bar) contained in a namespace.
/// This is agnostic to the scope of the name
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum Name<'ty> {
    Ident(String, Vec<Ty<'ty>>),
    Namespace(String, Vec<Ty<'ty>>, Box<Name<'ty>>),
}

impl std::fmt::Display for Name<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Name::Ident(string, types) if types.is_empty() => write!(f, "{}", string),
            Name::Ident(string, types) => write!(f, "{}::<{}>", string, type_array_str(types)),
            Name::Namespace(string, types, name) if types.is_empty() => {
                write!(f, "{}::{}", string, name)
            }
            Name::Namespace(string, types, name) => {
                write!(f, "{}::<{}>::{}", string, type_array_str(types), name)
            }
        }
    }
}

impl<'ty> Name<'ty> {
    /// Return new Name `<self>::<end>`
    pub fn with_end(&self, end: Name<'ty>) -> Name<'ty> {
        match self {
            Name::Ident(name, types) => Name::Namespace(name.clone(), types.clone(), Box::new(end)),
            Name::Namespace(id, types, child) => {
                Name::Namespace(id.clone(), types.clone(), Box::new(child.with_end(end)))
            }
        }
    }

    pub fn is_ident(&self) -> bool {
        matches!(self, Name::Ident(_, _))
    }

    pub fn pop_end(&self) -> Option<Name<'ty>> {
        match self {
            Name::Ident(_, _) => None,
            Name::Namespace(id, types, child) if child.is_ident() => {
                Some(Name::Ident(id.clone(), types.clone()))
            }
            Name::Namespace(id, types, child) => Some(Name::Namespace(
                id.clone(),
                types.clone(),
                Box::new(child.pop_end()?),
            )),
        }
    }
}

/// The visibility of a symbol relative to its parent module
#[derive(Debug)]
pub enum SymbolVisibility {
    Public,
    Private,
}

/// Use instead of using `Symbol` directly because this contains information on
/// the visibility of a symbol.
#[derive(Debug)]
pub struct SymbolInfo<'ty> {
    pub visibility: SymbolVisibility,
    pub symbol: Symbol<'ty>,
}

impl SymbolInfo<'_> {
    pub fn new(visibility: SymbolVisibility, symbol: Symbol) -> SymbolInfo {
        SymbolInfo { visibility, symbol }
    }
}

/// A symbol which could be a module, struct or function.
#[derive(Debug)]
pub enum Symbol<'ty> {
    Mod {
        symbols: HashMap<String, SymbolInfo<'ty>>,
    },
    Struct {
        types: Vec<String>,
        members: HashMap<String, Ty<'ty>>,
        symbols: HashMap<String, SymbolInfo<'ty>>,
    },
    Fun {
        types: Vec<String>,
        params: Vec<(String, Ty<'ty>)>,
        return_type: Ty<'ty>,
    },
}

#[derive(Debug)]
pub enum SymbolDeclError {
    AlreadyExists,
    InvalidName,
}

#[derive(Debug)]
pub enum SymbolResolveErr {
    /// The symbol doesn't exist
    NoSuchSymbol,
    /// Type params were put on module
    TypeParamsOnMod,
    /// Missing type params
    MissingTypeParams,
}

impl<'ty> Symbol<'ty> {
    /// Declare (create a new) symbol with the given name where the given name
    /// is a path relative to the current symbol.
    ///
    /// For example, if the `declare` function is called on a module `foo` and the
    /// given name is `bar::fizz`, a the new symbol is added to the module `foo`
    /// and would have a global name of `foo::bar::fizz`
    pub fn declare(&mut self, name: &Name, symbol: SymbolInfo<'ty>) -> Result<(), SymbolDeclError> {
        match (name, self) {
            (Name::Ident(id, _), Symbol::Mod { symbols })
            | (Name::Ident(id, _), Symbol::Struct { symbols, .. }) => {
                if symbols.contains_key(id) {
                    Err(SymbolDeclError::AlreadyExists)
                } else {
                    symbols.insert(id.clone(), symbol);
                    Ok(())
                }
            }

            (Name::Namespace(id, _, name), Symbol::Mod { symbols })
            | (Name::Namespace(id, _, name), Symbol::Struct { symbols, .. }) => symbols
                .get_mut(id)
                .ok_or(SymbolDeclError::InvalidName)?
                .symbol
                .declare(name, symbol),
            _ => Err(SymbolDeclError::InvalidName),
        }
    }

    /// Gets the type of a given named type.
    /// For example, given the following code:
    /// ```ignore
    /// struct<T> Node {
    ///     data: T,
    ///     next: *Node::<T>,
    /// }
    /// ```
    ///
    /// calling `resolve_ty("Node::<i32>")` should return a type in the format
    /// ```ignore
    /// ty::Struct {
    ///     name: "Node",
    ///     params: [ty::I32],
    ///     members: [
    ///         "data": ty::Param("T"),
    ///         "next": // oh shit forgot about inf
    ///     ]
    /// }
    /// ```
    pub fn resolve_ty(
        &self,
        name: &Name<'ty>,
        ctx: TyCtx<'ty>,
    ) -> Result<Ty<'ty>, SymbolResolveErr> {
        todo!()
    }

    /// Get a reference to the symbol at the given name (relative to self)
    pub fn resolve(&self, name: &Name<'ty>) -> Result<&SymbolInfo<'ty>, SymbolResolveErr> {
        use SymbolResolveErr::*;
        match (name, self) {
            (Name::Ident(id, types), Symbol::Mod { symbols }) if types.is_empty() => {
                symbols.get(id).ok_or(NoSuchSymbol)
            }

            (Name::Ident(id, _), Symbol::Mod { symbols }) => Err(TypeParamsOnMod),

            // If ident on struct type, we are getting member function
            (Name::Ident(id, name_types), Symbol::Struct { types, symbols, .. }) => {
                if name_types.len() != types.len() {
                    Err(MissingTypeParams)
                } else {
                    symbols.get(id).ok_or(NoSuchSymbol)
                }
            }

            // Here we are getting a member of a child
            (Name::Namespace(id, _, name), Symbol::Mod { symbols })
            | (Name::Namespace(id, _, name), Symbol::Struct { symbols, .. }) => {
                symbols.get(id).ok_or(NoSuchSymbol)?.symbol.resolve(name)
            }
            _ => Err(NoSuchSymbol),
        }
    }

    /// Get a mutable reference to the symbol at the given name (relative to self)
    pub fn resolve_mut(&mut self, name: &Name<'ty>) -> Option<&mut SymbolInfo<'ty>> {
        match (name, self) {
            (Name::Ident(id, _), Symbol::Mod { symbols })
            | (Name::Ident(id, _), Symbol::Struct { symbols, .. }) => symbols.get_mut(id),

            (Name::Namespace(id, _, name), Symbol::Mod { symbols })
            | (Name::Namespace(id, _, name), Symbol::Struct { symbols, .. }) => {
                symbols.get_mut(id)?.symbol.resolve_mut(name)
            }
            _ => None,
        }
    }
}
