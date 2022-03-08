//! Handles generation of the IR

mod case;
mod expr;
mod helpers;
mod scope;
mod stmt;

use crate::error_context::ErrorContext;
use crate::ir::{self, Def, DefId, DefKind, Module, Path};
use crate::mod_gen::{ModGenError, TypeGenerator};
use crate::tir;
use crate::ty::{Ty, TyCtx};
use scope::*;
use std::collections::HashMap;

type LowerResult<T> = Result<T, ModGenError>;

#[allow(clippy::too_many_arguments)]
pub fn lower_tir<'ty, 'mg>(
    usages: &'mg HashMap<String, Path>,
    module: &'mg Module<'ty>,
    db_name: String,
    err: &'mg mut ErrorContext,
    def_id: DefId,
    params: Vec<(String, Ty<'ty>)>,
    current_generics: Vec<String>,
    stmt: tir::Stmt<'ty>,
    tir: tir::TirCtx<'ty>,
) -> Result<ir::Fun<'ty>, ModGenError> {
    let (block, variable_defs) = {
        let mut gen = TirLower {
            usages,
            tcx: module.ty_ctx(),
            var_id: 0,
            md: module,
            err,
            scope: Box::new(Scope::from_params(params)),
            variable_defs: HashMap::new(),
            continue_break_label: Default::default(),
            label_next: None,
            current_generics,
            tir,
        };
        let body = gen.stmt(&stmt)?;
        let variable_defs = gen.variable_defs().into_iter().collect();
        (body, variable_defs)
    };
    Ok(ir::Fun {
        db_name,
        def_id,
        block,
        variable_defs,
    })
}

struct TirLower<'ty, 'mg> {
    md: &'mg Module<'ty>,
    tcx: TyCtx<'ty>,
    err: &'mg mut ErrorContext,
    usages: &'mg HashMap<String, Path>,
    scope: Box<Scope>,
    var_id: u32,
    variable_defs: HashMap<String, Ty<'ty>>,
    current_generics: Vec<String>,
    continue_break_label: Vec<String>,
    label_next: Option<String>,
    tir: tir::TirCtx<'ty>,
}
