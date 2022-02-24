use crate::ast::{self, TopStmt};
use crate::error_context::ErrorContext;
use crate::ir;
use crate::ir_gen;
use crate::symbol as sym;
use crate::ty;
use std::collections::HashMap;

pub struct ModGen<'ast, 'ty> {
    ast_module: &'ast ast::Module,
    module: ir::Module<'ty>,
    err: ErrorContext,
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

impl<'ast, 'ty> ModGen<'ast, 'ty> {
    fn gen_type(&mut self, ty: &'ast ast::Spanned<ast::Type>) -> Result<ty::Ty<'ty>, ModGenError> {
        todo!()
    }

    fn gen_name(&self, name: &'ast ast::Name) -> Result<sym::Name<'ty>, ModGenError> {
        todo!()
    }

    pub fn new(
        module: ir::Module<'ty>,
        err: ErrorContext,
        ast_module: &'ast ast::Module,
    ) -> ModGen<'ast, 'ty> {
        ModGen {
            ast_module,
            module,
            err,
            current_generics: Vec::new(),
        }
    }

    pub fn finish(self) -> (ir::Module<'ty>, ErrorContext) {
        (self.module, self.err)
    }

    /// declare
    fn declare(
        &mut self,
        name: &sym::Name<'ty>,
        symbol: sym::SymbolInfo<'ty>,
    ) -> Result<(), sym::SymbolDeclError> {
        self.module.root.declare(name, symbol)
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
        pub_tok: &'ast Option<ast::Span>,
        type_params: &'ast Vec<ast::Span>,
        ast_fun_name: &'ast ast::Spanned<ast::Name>,
        (self_type, params): &'ast ast::FunParams,
        return_type: &'ast Option<ast::SpanBox<ast::Type>>,
    ) -> Result<(), ModGenError> {
        self.current_generics.clear();
        self.current_generics
            .extend(type_params.iter().map(|p| p.str().into()));
        let fun_name: sym::Name = self.gen_name(ast_fun_name.value())?;
        let self_param: Option<ty::Ty<'ty>> = if self_type.is_some() {
            if fun_name.is_ident() {
                self.err.err(
                    format!("Functions with self type must be members of struct namespace"),
                    &ast_fun_name.span,
                );
                None
            } else {
                let struct_name = fun_name.pop_end().unwrap();
                match self.module.root.resolve(&struct_name) {
                    Ok(sym::SymbolInfo {
                        symbol: sym::Symbol::Struct { .. },
                        ..
                    }) => Some(
                        self.module
                            .root
                            .resolve_ty(&struct_name, self.module.ty_ctx())
                            .unwrap(),
                    ),
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

        let mut params_mapped = {
            let mut out = Vec::with_capacity(params.len());
            for ast::Spanned {
                value: (name, ty), ..
            } in params.iter()
            {
                out.push((
                    String::from(name.str()),
                    ModGen::<'ast, 'ty>::gen_type(self, ty)?,
                ));
            }
            out
        };

        fun_params.append(&mut params_mapped);
        let visibility = if pub_tok.is_some() {
            sym::SymbolVisibility::Public
        } else {
            sym::SymbolVisibility::Private
        };
        let return_type = match return_type {
            Some(ty) => self.gen_type(ty)?,
            None => ty::void_ty(self.module.ty_ctx()),
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
        ast_struct_name: &'ast ast::Spanned<ast::Name>,
        type_params: &'ast Vec<ast::Span>,
        members: &'ast ast::SpanVec<(ast::Ident, ast::SpanBox<ast::Type>)>,
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

        let sym = self.module.root.resolve_mut(&struct_name).unwrap();
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
        name: sym::Name<'ty>,
        body: &'ast ast::SpanBox<ast::FunBlock>,
    ) -> Result<(), ModGenError> {
        let (params, return_type, generics) = if let sym::Symbol::Fun {
            params,
            return_type,
            types,
        } =
            &self.module.root.resolve(&name).unwrap().symbol
        {
            (params.clone(), *return_type, types.clone())
        } else {
            unreachable!()
        };

        let body = ir_gen::gen_fun_block(
            &self.module,
            &mut self.err,
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
        todo!()
        // match name {
        //     sym::Name::Ident(_, params) => params.iter().all(|t| self.type_exists(t)),
        //     sym::Name::Namespace(_, params, next) => {
        //         params.iter().all(|t| self.type_exists(t)) && self.check_generics(next.as_ref())
        //     }
        // }
    }

    fn type_exists(&self, ty: &ty::Type) -> bool {
        todo!()
        // match ty {
        //     ty::Type::Named(name) => {
        //         self.check_generics(name)
        //             && match name {
        //                 sym::Name::Ident(id, params)
        //                     if params.is_empty() && self.current_generics.contains(id) =>
        //                 {
        //                     true
        //                 }
        //                 name => match self.module.ty_ctx.root.resolve(&name) {
        //                     Some(sym::SymbolInfo {
        //                         symbol: sym::Symbol::Struct { .. },
        //                         ..
        //                     })
        //                     | Some(sym::SymbolInfo {
        //                         symbol: sym::Symbol::Fun { .. },
        //                         ..
        //                     }) => true,
        //                     _ => false,
        //                 },
        //             }
        //     }
        //     ty::Type::Tuple(tys) => tys.iter().all(|ty| self.type_exists(ty)),
        //     ty::Type::Fun(params, ret) => {
        //         params.iter().all(|ty| self.type_exists(ty)) && self.type_exists(ret.as_ref())
        //     }
        //     ty::Type::Pointer(_, ty)
        //     | ty::Type::SizedArray(_, ty)
        //     | ty::Type::UnsizedArray(ty)
        //     | ty::Type::Range(ty)
        //     | ty::Type::Lhs(ty) => self.type_exists(ty.as_ref()),
        //     ty::Type::Primitive(_) | ty::Type::Err | ty::Type::Unknown => true,
        // }
    }
}
