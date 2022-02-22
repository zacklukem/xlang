use crate::ast;
use crate::const_eval::ConstEvaluator;
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

#[derive(Debug)]
pub struct TyCtx {
    pub root: Symbol,
}

/// Semantic type values
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Primitive(PrimitiveType),
    Named(Name),
    Pointer(PointerType, Box<Type>),
    Tuple(Vec<Type>),
    Fun(Vec<Type>, Box<Type>),
    SizedArray(usize, Box<Type>),
    UnsizedArray(Box<Type>),
    Range(Box<Type>),
    Lhs(Box<Type>),
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

    pub fn from_ast_type(ty: &ast::Type, const_eval: &ConstEvaluator) -> Self {
        let to_ast_type = |v: &ast::Spanned<ast::Type>| Type::from_ast_type(v.value(), const_eval);
        match ty {
            ast::Type::Primitive(ty) => Type::Primitive(ty.value().into()),
            ast::Type::Named(name) => Type::Named(name.value().into()),
            ast::Type::Pointer(ptr_type, inner_type) => {
                Type::Pointer(ptr_type.value().into(), Box::new(to_ast_type(inner_type)))
            }
            ast::Type::Tuple(_, types, _) => Type::Tuple(types.iter().map(to_ast_type).collect()),
            ast::Type::Fun(params, return_type) => Type::Fun(
                // Parameters
                params.iter().map(to_ast_type).collect(),
                // Return type (default to void)
                match return_type {
                    Some(return_type) => Box::new(to_ast_type(return_type)),
                    None => Box::new(Type::Primitive(PrimitiveType::Void)),
                },
            ),
            ast::Type::SizedArray {
                size, inner_type, ..
            } => Type::SizedArray(
                const_eval.eval_usize(size.value()),
                Box::new(Type::from_ast_type(inner_type.value(), const_eval)),
            ),
            ast::Type::UnsizedArray { inner_type, .. } => {
                Type::UnsizedArray(Box::new(to_ast_type(inner_type)))
            }
        }
    }
}

/// Represents a name (foo::bar) contained in a namespace.
/// This is agnostic to the scope of the name
#[derive(Debug, Clone, PartialEq)]
pub enum Name {
    Ident(String),
    Namespace(String, Box<Name>),
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Name::Ident(string) => write!(f, "{}", string),
            Name::Namespace(string, name) => write!(f, "{}::{}", string, name),
        }
    }
}

impl Name {
    /// Return new Name `<self>::<end>`
    pub fn with_end(&self, end: Name) -> Name {
        match self {
            Name::Ident(name) => Name::Namespace(name.clone(), Box::new(end)),
            Name::Namespace(id, child) => {
                Name::Namespace(id.clone(), Box::new(child.with_end(end)))
            }
        }
    }

    pub fn is_ident(&self) -> bool {
        matches!(self, Name::Ident(_))
    }

    pub fn pop_end(&self) -> Option<Name> {
        match self {
            Name::Ident(_) => None,
            Name::Namespace(id, child) if child.is_ident() => Some(Name::Ident(id.clone())),
            Name::Namespace(id, child) => {
                Some(Name::Namespace(id.clone(), Box::new(child.pop_end()?)))
            }
        }
    }
}

impl From<&ast::Name> for Name {
    fn from(name: &ast::Name) -> Self {
        match name {
            ast::Name::Ident(id) => Name::Ident(id.str().into()),
            ast::Name::Namespace(id, _, name) => {
                Name::Namespace(id.str().into(), Box::new(name.value().into()))
            }
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
        members: HashMap<String, Type>,
        symbols: HashMap<String, SymbolInfo>,
    },
    Fun {
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
            (Name::Ident(id), Symbol::Mod { symbols })
            | (Name::Ident(id), Symbol::Struct { symbols, .. }) => {
                if symbols.contains_key(id) {
                    Err(SymbolDeclError::AlreadyExists)
                } else {
                    symbols.insert(id.clone(), symbol);
                    Ok(())
                }
            }

            (Name::Namespace(id, name), Symbol::Mod { symbols })
            | (Name::Namespace(id, name), Symbol::Struct { symbols, .. }) => symbols
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
            (Name::Ident(id), Symbol::Mod { symbols })
            | (Name::Ident(id), Symbol::Struct { symbols, .. }) => symbols.get(id),

            (Name::Namespace(id, name), Symbol::Mod { symbols })
            | (Name::Namespace(id, name), Symbol::Struct { symbols, .. }) => {
                symbols.get(id)?.symbol.resolve(name)
            }
            _ => None,
        }
    }

    /// Get a mutable reference to the symbol at the given name (relative to self)
    pub fn resolve_mut(&mut self, name: &Name) -> Option<&mut SymbolInfo> {
        match (name, self) {
            (Name::Ident(id), Symbol::Mod { symbols })
            | (Name::Ident(id), Symbol::Struct { symbols, .. }) => symbols.get_mut(id),

            (Name::Namespace(id, name), Symbol::Mod { symbols })
            | (Name::Namespace(id, name), Symbol::Struct { symbols, .. }) => {
                symbols.get_mut(id)?.symbol.resolve_mut(name)
            }
            _ => None,
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
