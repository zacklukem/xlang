use either::Either;

use super::*;

fn continue_label(v: &str) -> String {
    format!("{}_continue", v)
}

fn break_label(v: &str) -> String {
    format!("{}_break", v)
}

impl<'ast, 'ty, 'mg> TypeGenerator<'ast, 'ty> for TirLower<'ty, 'mg> {
    fn current_generics(&self) -> &[String] {
        &self.current_generics
    }

    fn module(&self) -> &Module<'ty> {
        self.md
    }
    fn mod_path(&self) -> &Path {
        todo!();
    }

    fn usages(&self) -> &HashMap<String, Path> {
        self.usages
    }

    fn err(&mut self) -> &mut ErrorContext {
        self.err
    }
}

impl<'ty, 'ast, 'mg> TirLower<'ty, 'mg> {
    pub fn variable_defs(self) -> HashMap<String, Ty<'ty>> {
        self.variable_defs
    }

    pub fn get_var_id(&mut self) -> u32 {
        let n = self.var_id;
        self.var_id += 1;
        n
    }

    pub fn in_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let old_scope = std::mem::take(&mut self.scope);
        self.scope.parent = Some(old_scope);
        let r = f(self);
        let parent = std::mem::take(&mut self.scope.parent);
        self.scope = parent.unwrap();
        r
    }

    pub fn declare_var(&mut self, block_scope_name: &str, ty: Ty<'ty>) -> String {
        let id = self.get_var_id();
        let fun_scope_name = format!("{}_{}", block_scope_name, id);
        self.variable_defs.insert(fun_scope_name.clone(), ty);
        self.scope
            .insert(block_scope_name.into(), fun_scope_name.clone());
        fun_scope_name
    }

    pub fn declare_hidden_var(&mut self, ty: Ty<'ty>) -> String {
        let id = self.get_var_id();
        let fun_scope_name = format!("{}_{}", "hidden", id);
        self.variable_defs.insert(fun_scope_name.clone(), ty);
        fun_scope_name
    }

    pub fn label_next(&mut self, label: String) {
        assert!(self.label_next.is_none());
        self.label_next = Some(label);
    }

    pub fn replace_generics(&self, ty: Ty<'ty>, generics: &[(String, Ty<'ty>)]) -> Ty<'ty> {
        crate::generics::replace_generics(self.md.ty_ctx(), ty, generics)
    }

    /// Returns the type of the name and a boolean which is true if the name islocal scoped and false if it is global scoped
    pub fn resolve_value(&self, name: &Path, generics: &[Ty<'ty>]) -> Option<Either<String, Path>> {
        if let Path::Terminal(id) = name {
            if let Some(var) = self.scope.resolve(id) {
                return Some(Either::Left(var.clone()));
            }
        }
        match self.md.get_def_by_path(name) {
            Some(Def {
                kind:
                    DefKind::Fun {
                        ty_params,
                        params,
                        return_type,
                        ..
                    },
                ..
            }) => Some(Either::Right(name.clone())),
            _ => None,
        }
    }
}

pub fn map_to_vec<'a, K, T, F, I>(iter: I, fun: F) -> LowerResult<Vec<T>>
where
    F: FnMut(K) -> LowerResult<T>,
    K: 'a,
    I: IntoIterator<Item = K>,
{
    iter.into_iter().map(fun).collect::<LowerResult<Vec<T>>>()
}
