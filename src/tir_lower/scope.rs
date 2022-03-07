use super::*;

#[derive(Debug, Default)]
pub struct Scope {
    pub parent: Option<Box<Scope>>,
    /// Maps <String: block-scoped var name> to <String: function-scoped var name>
    variables: HashMap<String, String>,
}

impl Scope {
    pub fn from_params(params: Vec<(String, Ty<'_>)>) -> Self {
        Scope {
            parent: None,
            variables: params.into_iter().map(|(a, _)| (a.clone(), a)).collect(),
        }
    }

    pub fn resolve(&self, name: &str) -> Option<&String> {
        match self.variables.get(name) {
            Some(v) => Some(v),
            None => match &self.parent {
                Some(parent) => parent.resolve(name),
                None => None,
            },
        }
    }

    pub fn insert(&mut self, block_scope_name: String, fun_scope_name: String) -> Option<String> {
        self.variables.insert(block_scope_name, fun_scope_name)
    }
}
