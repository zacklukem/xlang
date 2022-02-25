//! Generates modules

use crate::ast::{self, TopStmt};
use crate::error_context::ErrorContext;
use crate::ir;
use crate::ir_gen;
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

pub trait TypeGenerator<'ast, 'ty> {
    fn current_generics(&self) -> &Vec<String>;
    fn module(&self) -> &ir::Module<'ty>;

    fn gen_type(&mut self, ty: &ast::Spanned<ast::Type>) -> Result<ty::Ty<'ty>, ModGenError> {
        let ty = match ty.value() {
            ast::Type::Primitive(pt) => ty::primitive_ty(self.module().ty_ctx(), pt.value().into()),
            ast::Type::Named(name) => {
                let (path, ty_params) = self.gen_path_and_generics(name.value())?;
                match path {
                    ir::Path::Terminal(st) if self.current_generics().contains(&st) => {
                        self.module().ty_ctx().int(ty::TyKind::Param(st))
                    }
                    _ => {
                        let def_id = self.module().get_def_id_by_path(&path).unwrap();
                        self.module()
                            .ty_ctx()
                            .int(ty::TyKind::Struct(ty::StructType {
                                def_id,
                                path,
                                ty_params,
                            }))
                    }
                }
            }
            ast::Type::Pointer(kind, ty) => self.module().ty_ctx().int(ty::TyKind::Pointer(
                kind.value().into(),
                self.gen_type(ty.as_ref())?,
            )),
            ast::Type::Tuple(_, tys, _) => self
                .module()
                .ty_ctx()
                .int(ty::TyKind::Tuple(self.gen_type_iter(tys.iter())?)),
            ast::Type::Fun(params, ret) => self.module().ty_ctx().int(ty::TyKind::Fun(
                self.gen_type_iter(params.iter())?,
                match ret {
                    Some(ret) => self.gen_type(ret)?,
                    None => ty::void_ty(self.module().ty_ctx()),
                },
            )),
            ast::Type::SizedArray {
                size, inner_type, ..
            } => self.module().ty_ctx().int(ty::TyKind::SizedArray(
                self.module().const_eval().eval_usize(size.value()),
                self.gen_type(inner_type)?,
            )),
            ast::Type::UnsizedArray { inner_type, .. } => self
                .module()
                .ty_ctx()
                .int(ty::TyKind::UnsizedArray(self.gen_type(inner_type)?)),
        };
        Ok(ty)
    }

    fn gen_type_iter<'a, T>(&mut self, iter: T) -> Result<Vec<ty::Ty<'ty>>, ModGenError>
    where
        T: std::iter::Iterator<Item = &'a ast::Spanned<ast::Type>>,
    {
        let mut out = Vec::with_capacity(iter.size_hint().0);
        for ty in iter {
            out.push(self.gen_type(ty)?);
        }
        Ok(out)
    }

    fn gen_path(&self, name: &'ast ast::Name) -> Result<ir::Path, ModGenError> {
        match name {
            ast::Name::Ident(id, _) => Ok(ir::Path::Terminal(id.str().into())),
            ast::Name::Namespace(id, _, _, next) => Ok(ir::Path::Namespace(
                id.str().into(),
                Box::new(self.gen_path(next.value())?),
            )),
        }
    }

    fn gen_path_and_generics(
        &mut self,
        name: &ast::Name,
    ) -> Result<(ir::Path, Vec<ty::Ty<'ty>>), ModGenError> {
        match name {
            ast::Name::Ident(id, generics) => Ok((
                ir::Path::Terminal(id.str().into()),
                self.gen_type_iter(generics.iter())?,
            )),
            ast::Name::Namespace(id, _, _, next) => {
                let (next, generics) = self.gen_path_and_generics(next.value())?;
                Ok((
                    ir::Path::Namespace(id.str().into(), Box::new(next)),
                    generics,
                ))
            }
        }
    }
}

impl<'ast, 'ty> TypeGenerator<'ast, 'ty> for ModGen<'ast, 'ty> {
    fn current_generics(&self) -> &Vec<String> {
        &self.current_generics
    }

    fn module(&self) -> &ir::Module<'ty> {
        &self.module
    }
}

impl<'ast, 'ty> ModGen<'ast, 'ty> {
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
                    let path = self.gen_path(name.value())?;
                    let def = ir::Def::new(
                        if pub_tok.is_some() {
                            ir::DefVisibility::Public
                        } else {
                            ir::DefVisibility::Private
                        },
                        ir::DefKind::Struct {
                            symbols: Default::default(),
                            members: Default::default(),
                            // TODO: insert these
                            ty_params: type_params.iter().map(|v| v.str().into()).collect(),
                        },
                    );
                    self.module.declare(path, def).unwrap();
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
                TopStmt::FunDecl {
                    pub_tok,
                    type_params,
                    name,
                    params,
                    return_type,
                    ..
                } => self.define_fun_type(true, pub_tok, type_params, name, params, return_type)?,
                TopStmt::Fun {
                    pub_tok,
                    type_params,
                    name,
                    params,
                    return_type,
                    ..
                } => {
                    self.define_fun_type(false, pub_tok, type_params, name, params, return_type)?
                }
                _ => todo!(),
            }
        }
        Ok(())
    }

    fn get_fun_self_type(
        &mut self,
        span: &ast::Span,
        struct_name: &ir::Path,
        struct_generics: Vec<ty::Ty<'ty>>,
    ) -> Option<ty::Ty<'ty>> {
        match self.module.get_def_by_path(struct_name) {
            Some(ir::Def {
                kind: ir::DefKind::Struct { .. },
                ..
            }) => {
                let def_id = self.module.get_def_id_by_path(struct_name).unwrap();

                Some(
                    self.module
                        .ty_ctx()
                        .int(ty::TyKind::Struct(ty::StructType {
                            def_id,
                            path: struct_name.clone(),
                            ty_params: struct_generics,
                        }))
                        .ptr(self.module.ty_ctx()),
                )
            }
            _ => {
                self.err.err(
                    format!("Functions with self type must be members of struct namespace"),
                    span,
                );
                None
            }
        }
    }

    /// Define a function type in second pass
    fn define_fun_type(
        &mut self,
        external: bool,
        pub_tok: &'ast Option<ast::Span>,
        type_params: &'ast Vec<ast::Span>,
        ast_fun_name: &'ast ast::Spanned<ast::Name>,
        (self_type, params): &'ast ast::FunParams,
        return_type: &'ast Option<ast::SpanBox<ast::Type>>,
    ) -> Result<(), ModGenError> {
        self.current_generics.clear();
        self.current_generics
            .extend(type_params.iter().map(|p| p.str().into()));
        let fun_name = self.gen_path(ast_fun_name.value())?;
        let self_param: Option<ty::Ty<'ty>> = if self_type.is_some() {
            if fun_name.is_terminal() {
                self.err.err(
                    format!("Functions with self type must be members of struct namespace"),
                    &ast_fun_name.span,
                );
                None
            } else {
                let struct_name = ast_fun_name.value().pop_end().unwrap();
                let (struct_path, struct_generics) = self.gen_path_and_generics(&struct_name)?;
                self.get_fun_self_type(&ast_fun_name.span, &struct_path, struct_generics)
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
            ir::DefVisibility::Public
        } else {
            ir::DefVisibility::Private
        };
        let return_type = match return_type {
            Some(ty) => self.gen_type(ty)?,
            None => ty::void_ty(self.module.ty_ctx()),
        };
        let def = ir::DefKind::Fun {
            external,
            params: fun_params,
            return_type,
            // TODO: insert these
            ty_params: self.current_generics.clone(),
        };
        self.module
            .declare(fun_name, ir::Def::new(visibility, def))
            .unwrap();
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
        let struct_path = self.gen_path(ast_struct_name.value())?;

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

        let sym = self.module.get_mut_def_by_path(&struct_path).unwrap();
        if let ir::DefKind::Struct { members, .. } = &mut sym.kind {
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
                    let path = self.gen_path(name.value())?;
                    self.gen_fun_ir(path, body)?;
                }
                _ => (),
            }
        }
        Ok(())
    }

    fn gen_fun_ir(
        &mut self,
        path: ir::Path,
        body: &'ast ast::SpanBox<ast::FunBlock>,
    ) -> Result<(), ModGenError> {
        let (params, return_type, generics) = if let ir::DefKind::Fun {
            params,
            return_type,
            ty_params,
            ..
        } =
            &self.module.get_def_by_path(&path).unwrap().kind
        {
            (params.clone(), *return_type, ty_params.clone())
        } else {
            unreachable!()
        };

        let def_id = self.module.get_def_id_by_path(&path).unwrap();

        let body = ir_gen::gen_fun_block(
            &self.module,
            format!("{}", path),
            &mut self.err,
            def_id,
            params,
            return_type,
            body,
            generics,
        )?;

        self.module.functions.insert(def_id, body);

        Ok(())
    }
}
