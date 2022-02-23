use crate::ast::{self, TopStmt};
use crate::error_context::ErrorContext;
use crate::ir;
use crate::ir_gen;
use crate::symbol as sym;
use crate::ty;
use std::collections::HashMap;

pub struct ModGen<'mg> {
    ast_module: &'mg ast::Module,
    module: &'mg mut ir::Module,
    err: &'mg mut ErrorContext,
    current_generics: Vec<String>,
}

#[derive(Debug)]
pub enum ModGenError {
    UnableToDeclare,
}

impl From<sym::SymbolDeclError> for ModGenError {
    fn from(sde: sym::SymbolDeclError) -> Self {
        match sde {
            sym::SymbolDeclError::AlreadyExists => ModGenError::UnableToDeclare,
            sym::SymbolDeclError::InvalidName => ModGenError::UnableToDeclare,
        }
    }
}

impl<'mg> ModGen<'mg> {
    fn gen_type(&mut self, ty: &ast::Spanned<ast::Type>) -> Result<ty::Type, ModGenError> {
        let span = ty.span.clone();
        let ty = ty::Type::from_ast_type(ty.value(), self.module.const_eval());
        if self.type_exists(&ty) {
            Ok(ty)
        } else {
            self.err.err(format!("Invalid type {}", ty), &span);
            Ok(ty::Type::Err)
        }
    }

    fn gen_name(&self, name: &ast::Name) -> Result<sym::Name, ModGenError> {
        Ok(sym::Name::from_ast_name(name, self.module.const_eval()))
    }

    pub fn new(
        module: &'mg mut ir::Module,
        err: &'mg mut ErrorContext,
        ast_module: &'mg ast::Module,
    ) -> ModGen<'mg> {
        ModGen {
            ast_module,
            module,
            err,
            current_generics: Vec::new(),
        }
    }

    /// declare
    fn declare(
        &mut self,
        name: &sym::Name,
        symbol: sym::SymbolInfo,
    ) -> Result<(), sym::SymbolDeclError> {
        self.module.ty_ctx_mut().root.declare(name, symbol)
    }

    pub fn run(&mut self) -> Result<(), ModGenError> {
        self.declare_types()?;
        self.define_types()?;
        self.gen_ir()?;
        Ok(())
    }

    /// First pass, declare all struct types
    fn declare_types(&mut self) -> Result<(), ModGenError> {
        for stmt in &self.ast_module.top_stmts {
            let stmt = &stmt.value;
            match stmt {
                TopStmt::Struct {
                    pub_tok,
                    type_params,
                    name,
                    ..
                } => {
                    let name = self.gen_name(name.value())?;
                    let symbol = sym::SymbolInfo::new(
                        if pub_tok.is_some() {
                            sym::SymbolVisibility::Public
                        } else {
                            sym::SymbolVisibility::Private
                        },
                        sym::Symbol::Struct {
                            symbols: Default::default(),
                            members: Default::default(),
                            // TODO: insert these
                            types: type_params.iter().map(|v| v.str().into()).collect(),
                        },
                    );
                    self.declare(&name, symbol)
                        .map_err(Into::<ModGenError>::into)?;
                }
                // ignore other top level stmts
                _ => (),
            }
        }
        Ok(())
    }

    /// second pass, define all types (including function types)
    fn define_types(&mut self) -> Result<(), ModGenError> {
        for stmt in &self.ast_module.top_stmts {
            let stmt = &stmt.value;
            match stmt {
                // Define struct types
                TopStmt::Struct {
                    name,
                    type_params,
                    members,
                    ..
                } => self.define_struct(name, type_params, members)?,
                TopStmt::Fun {
                    pub_tok,
                    type_params,
                    name,
                    params,
                    return_type,
                    ..
                } => self.define_fun_type(pub_tok, type_params, name, params, return_type)?,
            }
        }
        Ok(())
    }

    /// Define a function type in second pass
    fn define_fun_type(
        &mut self,
        pub_tok: &Option<ast::Span>,
        type_params: &Vec<ast::Span>,
        ast_fun_name: &ast::Spanned<ast::Name>,
        (self_type, params): &ast::FunParams,
        return_type: &Option<ast::SpanBox<ast::Type>>,
    ) -> Result<(), ModGenError> {
        self.current_generics.clear();
        self.current_generics
            .extend(type_params.iter().map(|p| p.str().into()));
        let fun_name: sym::Name = self.gen_name(ast_fun_name.value())?;
        let self_param = if self_type.is_some() {
            if fun_name.is_ident() {
                self.err.err(
                    format!("Functions with self type must be members of struct namespace"),
                    &ast_fun_name.span,
                );
                None
            } else {
                let struct_name = fun_name.pop_end().unwrap();
                match self.module.ty_ctx().root.resolve(&struct_name) {
                    Some(symbol_info)
                        if matches!(symbol_info.symbol, sym::Symbol::Struct { .. }) =>
                    {
                        Some(ty::Type::Named(struct_name).ptr())
                    }
                    _ => {
                        self.err.err(
                            format!("Functions with self type must be members of struct namespace"),
                            &ast_fun_name.span,
                        );
                        None
                    }
                }
            }
        } else {
            None
        };
        let mut fun_params = if let Some(ty) = self_param {
            vec![(String::from("self"), ty)]
        } else {
            vec![]
        };
        let mut params_mapped = params
            .iter()
            .map(ast::Spanned::value)
            .map(|(name, ty)| Ok((String::from(name.str()), self.gen_type(ty)?)))
            .collect::<Result<Vec<_>, ModGenError>>()?;

        fun_params.append(&mut params_mapped);
        let visibility = if pub_tok.is_some() {
            sym::SymbolVisibility::Public
        } else {
            sym::SymbolVisibility::Private
        };
        let return_type = match return_type {
            Some(ty) => Box::new(self.gen_type(ty.as_ref())?),
            None => Box::new(ty::Type::Primitive(sym::PrimitiveType::Void)),
        };
        let symbol = sym::Symbol::Fun {
            params: fun_params,
            return_type,
            // TODO: insert these
            types: self.current_generics.clone(),
        };
        self.declare(&fun_name, sym::SymbolInfo::new(visibility, symbol))?;
        self.current_generics.clear();
        Ok(())
    }

    /// Define a struct in second pass
    fn define_struct(
        &mut self,
        ast_struct_name: &ast::Spanned<ast::Name>,
        type_params: &Vec<ast::Span>,
        members: &ast::SpanVec<(ast::Ident, ast::SpanBox<ast::Type>)>,
    ) -> Result<(), ModGenError> {
        self.current_generics.clear();
        self.current_generics
            .extend(type_params.iter().map(|p| p.str().into()));
        let struct_name = self.gen_name(ast_struct_name.value())?;

        let mut sym_members = HashMap::new();

        for spanned_member in members.iter() {
            let (field_name, field_type) = &spanned_member.value;
            let ty = self.gen_type(field_type.as_ref())?;
            let name = field_name.str().into();
            if sym_members.contains_key(&name) {
                self.err.err(
                    format!(
                        "The struct {:?} already contains a member named {}",
                        ast_struct_name.value, name
                    ),
                    &field_name.span,
                )
            } else {
                sym_members.insert(name, ty);
            }
        }

        let sym = self.module.ty_ctx.root.resolve_mut(&struct_name).unwrap();
        if let sym::Symbol::Struct { members, .. } = &mut sym.symbol {
            *members = sym_members;
        } else {
            panic!("Inconsistent define/declare passes");
        }
        self.current_generics.clear();
        Ok(())
    }

    fn gen_ir(&mut self) -> Result<(), ModGenError> {
        for stmt in &self.ast_module.top_stmts {
            match &stmt.value {
                ast::TopStmt::Fun { name, body, .. } => {
                    let name = self.gen_name(name.value())?;
                    self.gen_fun_ir(name, body)?;
                }
                _ => (),
            }
        }
        Ok(())
    }

    fn gen_fun_ir(
        &mut self,
        name: sym::Name,
        body: &ast::SpanBox<ast::FunBlock>,
    ) -> Result<(), ModGenError> {
        let fun_type = &self.module.ty_ctx.root.resolve(&name).unwrap().symbol;
        let (params, return_type, generics) = if let sym::Symbol::Fun {
            params,
            return_type,
            types,
        } = fun_type
        {
            (params, return_type, types)
        } else {
            unreachable!()
        };

        let body = ir_gen::gen_fun_block(
            self.module,
            self.err,
            &name,
            params,
            return_type,
            body,
            generics.clone(),
        )?;

        self.module.functions.push(body);

        Ok(())
    }

    fn check_generics(&self, name: &sym::Name) -> bool {
        match name {
            sym::Name::Ident(_, params) => params.iter().all(|t| self.type_exists(t)),
            sym::Name::Namespace(_, params, next) => {
                params.iter().all(|t| self.type_exists(t)) && self.check_generics(next.as_ref())
            }
        }
    }

    fn type_exists(&self, ty: &ty::Type) -> bool {
        match ty {
            ty::Type::Named(name) => {
                self.check_generics(name)
                    && match name {
                        sym::Name::Ident(id, params)
                            if params.is_empty() && self.current_generics.contains(id) =>
                        {
                            true
                        }
                        name => match self.module.ty_ctx.root.resolve(&name) {
                            Some(sym::SymbolInfo {
                                symbol: sym::Symbol::Struct { .. },
                                ..
                            })
                            | Some(sym::SymbolInfo {
                                symbol: sym::Symbol::Fun { .. },
                                ..
                            }) => true,
                            _ => false,
                        },
                    }
            }
            ty::Type::Tuple(tys) => tys.iter().all(|ty| self.type_exists(ty)),
            ty::Type::Fun(params, ret) => {
                params.iter().all(|ty| self.type_exists(ty)) && self.type_exists(ret.as_ref())
            }
            ty::Type::Pointer(_, ty)
            | ty::Type::SizedArray(_, ty)
            | ty::Type::UnsizedArray(ty)
            | ty::Type::Range(ty)
            | ty::Type::Lhs(ty) => self.type_exists(ty.as_ref()),
            ty::Type::Primitive(_) | ty::Type::Err | ty::Type::Unknown => true,
        }
    }
}
