use log::debug;

use crate::generics::replace_generics;
use crate::ir::{DefId, DefKind, Expr, ExprKind, ExternKind, Module, Stmt, StmtKind};
use crate::ty::{AdtType, Ty, TyKind};
use std::collections::{HashMap, HashSet};
use std::iter::Iterator;

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct DefInstance<'ty> {
    pub def_id: DefId,
    pub ty_params: Vec<Ty<'ty>>,
}

impl<'ty> DefInstance<'ty> {
    pub fn new(def_id: DefId, ty_params: Vec<Ty<'ty>>) -> DefInstance<'ty> {
        DefInstance { def_id, ty_params }
    }
}

#[derive(Debug)]
pub struct Monomorphize<'ty> {
    module: &'ty Module<'ty>,
    monos: HashSet<DefInstance<'ty>>,
    special_types: HashSet<Ty<'ty>>,
}

impl<'ty> Monomorphize<'ty> {
    pub fn new(module: &'ty Module<'ty>) -> Monomorphize<'ty> {
        Monomorphize {
            module,
            monos: HashSet::new(),
            special_types: HashSet::new(),
        }
    }

    pub fn finish(self) -> (HashSet<DefInstance<'ty>>, HashSet<Ty<'ty>>) {
        (self.monos, self.special_types)
    }

    pub fn run(&mut self) {
        for (def_id, def) in self.module.defs_iter() {
            match &def.kind {
                DefKind::Fun {
                    ty_params,
                    params,
                    return_type,
                    external,
                } if ty_params.is_empty() => self.fun_def(
                    *external,
                    *def_id,
                    ty_params,
                    &Vec::new(),
                    params,
                    return_type,
                ),
                DefKind::Struct {
                    ty_params,
                    members,
                    symbols,
                } if ty_params.is_empty() => {
                    self.struct_def(*def_id, ty_params, &Vec::new(), members, symbols)
                }
                _ => (),
            }
        }
    }

    pub fn mono_def_id(&mut self, def_id: DefId, ty_params_types: &[Ty<'ty>]) {
        match &self.module.get_def_by_id(def_id).kind {
            DefKind::Fun {
                ty_params,
                params,
                return_type,
                external,
            } => self.fun_def(
                *external,
                def_id,
                ty_params,
                ty_params_types,
                params,
                return_type,
            ),
            DefKind::Struct {
                ty_params,
                members,
                symbols,
            } => self.struct_def(def_id, ty_params, ty_params_types, members, symbols),
            _ => (),
        }
    }

    pub fn print_instances(&self) {
        for mono in &self.monos {
            let path = self.module.get_path_by_def_id(mono.def_id);
            debug!("{} {:?}", path, mono.ty_params);
        }
    }

    pub fn mono_ty(&mut self, ty: Ty<'ty>) {
        use TyKind::*;
        match ty.0 .0 {
            Pointer(_, inner) | SizedArray(_, inner) | UnsizedArray(inner) | Range(inner) => {
                self.mono_ty(*inner)
            }
            Tuple(tys) => {
                self.special_types.insert(ty);
                for ty in tys {
                    self.mono_ty(*ty);
                }
            }
            Fun(params, ret) => {
                self.mono_ty(*ret);
                for ty in params {
                    self.mono_ty(*ty);
                }
            }
            Adt(AdtType {
                def_id,
                ty_params: passed_ty_params,
                ..
            }) => {
                match &self.module.get_def_by_id(*def_id).kind {
                    DefKind::Struct {
                        ty_params: named_ty_params,
                        members,
                        symbols,
                    } => {
                        assert_eq!(named_ty_params.len(), passed_ty_params.len());
                        self.struct_def(
                            *def_id,
                            named_ty_params,
                            passed_ty_params,
                            members,
                            symbols,
                        );
                    }
                    DefKind::Enum {
                        ty_params: named_ty_params,
                        variants,
                        symbols,
                    } => {
                        assert_eq!(named_ty_params.len(), passed_ty_params.len());
                        self.enum_def(
                            *def_id,
                            named_ty_params,
                            passed_ty_params,
                            variants,
                            symbols,
                        );
                    }
                    _ => panic!("err"),
                }
                // self.mono
            }
            Param(_) => (),
            _ => (),
        }
    }

    pub fn fun_def(
        &mut self,
        external: ExternKind,
        def_id: DefId,
        ty_params_names: &[String],
        ty_params_types: &[Ty<'ty>],
        params: &[(String, Ty<'ty>)],
        return_type: &Ty<'ty>,
    ) {
        if self
            .monos
            .insert(DefInstance::new(def_id, ty_params_types.into()))
        {
            let path = self.module.get_path_by_def_id(def_id);
            debug!("Monomorphize {} {:?}", path, ty_params_names);
            assert_eq!(ty_params_names.len(), ty_params_types.len());
            let ty_params = Iterator::zip(
                ty_params_names.iter().cloned(),
                ty_params_types.iter().cloned(),
            )
            .collect::<Vec<_>>();
            let return_type = replace_generics(self.module.ty_ctx(), *return_type, &ty_params);
            let params_iter = params
                .iter()
                .map(|(_, ty)| replace_generics(self.module.ty_ctx(), *ty, &ty_params));

            self.mono_ty(return_type);
            for param in params_iter {
                self.mono_ty(param);
            }
            if external == ExternKind::Define {
                self.fun_body(def_id, &ty_params);
            }
        }
    }

    pub fn fun_body(&mut self, def_id: DefId, ty_params: &[(String, Ty<'ty>)]) {
        let fun = self.module.functions.get(&def_id).unwrap();
        for (_, ty) in &fun.variable_defs {
            let ty = replace_generics(self.module.ty_ctx(), *ty, ty_params);
            self.mono_ty(ty);
        }

        self.stmt(&fun.block, ty_params);
    }

    pub fn stmt(&mut self, stmt: &Stmt<'ty>, ty_params: &[(String, Ty<'ty>)]) {
        use StmtKind::*;
        match &stmt.kind {
            If {
                condition,
                block,
                else_block,
            } => {
                self.expr(condition, ty_params);
                self.stmt(block, ty_params);
                if let Some(else_block) = else_block {
                    self.stmt(else_block, ty_params);
                }
            }
            While { condition, block } => {
                self.expr(condition, ty_params);
                self.stmt(block, ty_params);
            }
            For {
                initializer,
                condition,
                incrementor,
                block,
            } => {
                self.stmt(initializer, ty_params);
                self.expr(condition, ty_params);
                self.expr(incrementor, ty_params);
                self.stmt(block, ty_params);
            }
            Labeled(_, stmt) => {
                if let Some(stmt) = stmt {
                    self.stmt(stmt, ty_params);
                }
            }
            StmtList(stmts) | Block(stmts) => {
                for stmt in stmts {
                    self.stmt(stmt, ty_params);
                }
            }
            Return(expr) => {
                if let Some(expr) = expr {
                    self.expr(expr, ty_params);
                }
            }
            Expr(expr) => {
                self.expr(expr, ty_params);
            }
            Switch {
                expr,
                cases,
                default,
            } => {
                self.expr(expr, ty_params);
                for (det, stmt) in cases {
                    self.expr(det, ty_params);
                    self.stmt(stmt, ty_params);
                }
                if let Some(default) = default {
                    self.stmt(default, ty_params);
                }
            }
            InlineC { .. } | Goto(_) => (),
        }
    }

    pub fn expr(&mut self, expr: &Expr<'ty>, ty_params: &[(String, Ty<'ty>)]) {
        use ExprKind::*;
        debug!("expr {:?}", ty_params);
        let ty = replace_generics(self.module.ty_ctx(), self.module.ty_of(expr), ty_params);
        self.mono_ty(ty);
        match &expr.kind {
            Discriminant(inner)
            | GetVariant(inner, _)
            | TupleValue(inner, _)
            | Unary(_, inner)
            | Dot(inner, _)
            | RangeFrom(inner) => {
                self.expr(inner, ty_params);
            }
            Array { members: exprs } | Tuple(exprs) => {
                for expr in exprs {
                    self.expr(expr, ty_params);
                }
            }
            Assign(lhs, _, rhs) | Range(lhs, rhs) | Binary(lhs, _, rhs) => {
                self.expr(lhs, ty_params);
                self.expr(rhs, ty_params);
            }
            Cast(lhs, ty) => {
                self.expr(lhs, ty_params);
                let ty = replace_generics(self.module.ty_ctx(), *ty, ty_params);
                self.mono_ty(ty);
            }
            GlobalIdent(path, generics) => {
                let def_id = self.module.get_def_id_by_path(path).unwrap();
                let generics = generics
                    .iter()
                    .map(|ty| replace_generics(self.module.ty_ctx(), *ty, ty_params))
                    .collect::<Vec<_>>();
                self.mono_def_id(def_id, &generics);
            }
            Ternary {
                condition,
                then_expr,
                else_expr,
            } => {
                self.expr(condition, ty_params);
                self.expr(then_expr, ty_params);
                self.expr(else_expr, ty_params);
            }
            Call { expr, arguments } => {
                self.expr(expr, ty_params);
                for expr in arguments {
                    self.expr(expr, ty_params);
                }
            }
            Index { expr, index } => {
                self.expr(expr, ty_params);
                self.expr(index, ty_params);
            }
            Struct { ty, members } => {
                let ty = replace_generics(self.module.ty_ctx(), *ty, ty_params);
                self.mono_ty(ty);
                for (_, expr) in members {
                    self.expr(expr, ty_params);
                }
            }
            DiscriminantValue(_) | Ident(_) | Integer(_) | Float(_) | String(_) | Bool(_)
            | Null | Err => (),
        }
    }

    pub fn enum_def(
        &mut self,
        def_id: DefId,
        ty_params_names: &[String],
        ty_params_types: &[Ty<'ty>],
        variants: &HashMap<String, Ty<'ty>>,
        _symbols: &HashMap<String, DefId>,
    ) {
        if self
            .monos
            .insert(DefInstance::new(def_id, ty_params_types.into()))
        {
            assert_eq!(ty_params_names.len(), ty_params_types.len());
            let ty_params = Iterator::zip(
                ty_params_names.iter().cloned(),
                ty_params_types.iter().cloned(),
            )
            .collect::<Vec<_>>();

            let variants_iter = variants
                .values()
                .map(|ty| replace_generics(self.module.ty_ctx(), *ty, &ty_params));

            for variant in variants_iter {
                self.mono_ty(variant);
            }
        }
    }

    pub fn struct_def(
        &mut self,
        def_id: DefId,
        ty_params_names: &[String],
        ty_params_types: &[Ty<'ty>],
        members: &HashMap<String, Ty<'ty>>,
        _symbols: &HashMap<String, DefId>,
    ) {
        if self
            .monos
            .insert(DefInstance::new(def_id, ty_params_types.into()))
        {
            assert_eq!(ty_params_names.len(), ty_params_types.len());
            let ty_params = Iterator::zip(
                ty_params_names.iter().cloned(),
                ty_params_types.iter().cloned(),
            )
            .collect::<Vec<_>>();

            let members_iter = members
                .values()
                .map(|ty| replace_generics(self.module.ty_ctx(), *ty, &ty_params));

            for member in members_iter {
                self.mono_ty(member);
            }
        }
    }
}
