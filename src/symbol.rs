use crate::ast;
use crate::const_eval::ConstEvaluator;
use crate::ir_display::type_array_str;
use crate::ty::Type;
use std::collections::HashMap;

#[derive(Debug)]
pub struct TyCtx {
    pub root: Symbol,
}

/// Represents a name (foo::bar) contained in a namespace.
/// This is agnostic to the scope of the name
#[derive(Debug, Clone, PartialEq)]
pub enum Name {
    Ident(String, Vec<Type>),
    Namespace(String, Vec<Type>, Box<Name>),
}

impl std::fmt::Display for Name {
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

impl Name {
    /// Return new Name `<self>::<end>`
    pub fn with_end(&self, end: Name) -> Name {
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

    pub fn pop_end(&self) -> Option<Name> {
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
pub struct SymbolInfo {
    pub visibility: SymbolVisibility,
    pub symbol: Symbol,
}

impl SymbolInfo {
    pub fn new(visibility: SymbolVisibility, symbol: Symbol) -> SymbolInfo {
        SymbolInfo { visibility, symbol }
    }
}

/// A symbol which could be a module, struct or function.
#[derive(Debug)]
pub enum Symbol {
    Mod {
        symbols: HashMap<String, SymbolInfo>,
    },
    Struct {
        types: Vec<String>,
        members: HashMap<String, Type>,
        symbols: HashMap<String, SymbolInfo>,
    },
    Fun {
        types: Vec<String>,
        params: Vec<(String, Type)>,
        return_type: Box<Type>,
    },
}

#[derive(Debug)]
pub enum SymbolDeclError {
    AlreadyExists,
    InvalidName,
}

impl Symbol {
    /// Declare (create a new) symbol with the given name where the given name
    /// is a path relative to the current symbol.
    ///
    /// For example, if the `declare` function is called on a module `foo` and the
    /// given name is `bar::fizz`, a the new symbol is added to the module `foo`
    /// and would have a global name of `foo::bar::fizz`
    pub fn declare(&mut self, name: &Name, symbol: SymbolInfo) -> Result<(), SymbolDeclError> {
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

    /// Get a reference to the symbol at the given name (relative to self)
    pub fn resolve(&self, name: &Name) -> Option<&SymbolInfo> {
        match (name, self) {
            (Name::Ident(id, _), Symbol::Mod { symbols })
            | (Name::Ident(id, _), Symbol::Struct { symbols, .. }) => symbols.get(id),

            (Name::Namespace(id, _, name), Symbol::Mod { symbols })
            | (Name::Namespace(id, _, name), Symbol::Struct { symbols, .. }) => {
                symbols.get(id)?.symbol.resolve(name)
            }
            _ => None,
        }
    }

    /// Get a mutable reference to the symbol at the given name (relative to self)
    pub fn resolve_mut(&mut self, name: &Name) -> Option<&mut SymbolInfo> {
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
