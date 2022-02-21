use crate::ast::{self, TopStmt};
use crate::error_context::ErrorContext;
use crate::ir;
use crate::ir_gen;
use crate::symbol as sym;

pub struct ModGen<'mg> {
    ast_module: &'mg ast::Module,
    module: &'mg mut ir::Module,
    err: &'mg mut ErrorContext,
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
    pub fn new(
        module: &'mg mut ir::Module,
        err: &'mg mut ErrorContext,
        ast_module: &'mg ast::Module,
    ) -> ModGen<'mg> {
        ModGen {
            ast_module,
            module,
            err,
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
                TopStmt::Struct { pub_tok, name, .. } => {
                    let name = name.value().into();
                    let symbol = sym::SymbolInfo::new(
                        if pub_tok.is_some() {
                            sym::SymbolVisibility::Public
                        } else {
                            sym::SymbolVisibility::Private
                        },
                        sym::Symbol::Struct {
                            symbols: Default::default(),
                            members: Default::default(),
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
                TopStmt::Struct { name, members, .. } => self.define_struct(name, members)?,
                TopStmt::Fun {
                    pub_tok,
                    name,
                    params,
                    return_type,
                    ..
                } => self.define_fun_type(pub_tok, name, params, return_type)?,
            }
        }
        Ok(())
    }

    /// Define a function type in second pass
    fn define_fun_type(
        &mut self,
        pub_tok: &Option<ast::Span>,
        ast_fun_name: &ast::Spanned<ast::Name>,
        (self_type, params): &ast::FunParams,
        return_type: &Option<ast::SpanBox<ast::Type>>,
    ) -> Result<(), ModGenError> {
        let fun_name: sym::Name = ast_fun_name.value().into();
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
                        Some(sym::Type::Named(struct_name).ptr())
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
        let params_iter = params.iter().map(ast::Spanned::value).map(|(name, ty)| {
            (
                String::from(name.str()),
                sym::Type::from_ast_type(ty.value(), self.module.const_eval()),
            )
        });
        fun_params.extend(params_iter);
        let visibility = if pub_tok.is_some() {
            sym::SymbolVisibility::Public
        } else {
            sym::SymbolVisibility::Private
        };
        let return_type = match return_type {
            Some(ty) => Box::new(sym::Type::from_ast_type(
                ty.value(),
                self.module.const_eval(),
            )),
            None => Box::new(sym::Type::Primitive(sym::PrimitiveType::Void)),
        };
        let symbol = sym::Symbol::Fun {
            params: fun_params,
            return_type,
        };
        self.declare(&fun_name, sym::SymbolInfo::new(visibility, symbol))?;
        Ok(())
    }

    /// Define a struct in second pass
    fn define_struct(
        &mut self,
        ast_struct_name: &ast::Spanned<ast::Name>,
        members: &ast::SpanVec<(ast::Ident, ast::SpanBox<ast::Type>)>,
    ) -> Result<(), ModGenError> {
        let struct_name = ast_struct_name.value().into();
        let sym = self.module.ty_ctx.root.resolve_mut(&struct_name).unwrap();
        if let sym::Symbol::Struct {
            members: sym_members,
            ..
        } = &mut sym.symbol
        {
            for spanned_member in members.iter() {
                let (field_name, field_type) = &spanned_member.value;
                let ty = sym::Type::from_ast_type(field_type.value(), &self.module.const_eval);
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
        } else {
            panic!("Inconsistent define/declare passes");
        }
        Ok(())
    }

    fn gen_ir(&mut self) -> Result<(), ModGenError> {
        for stmt in &self.ast_module.top_stmts {
            match &stmt.value {
                ast::TopStmt::Fun { name, body, .. } => {
                    let name = name.value().into();
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
        let (params, return_type) = if let sym::Symbol::Fun {
            params,
            return_type,
        } = fun_type
        {
            (params, return_type)
        } else {
            unreachable!()
        };

        let body = ir_gen::gen_fun_block(self.module, self.err, &name, params, return_type, body)?;

        self.module.functions.push(body);

        Ok(())
    }
}
