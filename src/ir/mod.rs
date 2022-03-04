//! The IR data structures

pub mod ir_build;
pub mod ir_display;

use crate::ast::{self, Span};
use crate::const_eval::ConstEvaluator;
use crate::ty::{Ty, TyCtx};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ExprId(u32);

pub struct Fun<'ty> {
    pub def_id: DefId,
    pub db_name: String,
    pub variable_defs: Vec<(String, Ty<'ty>)>,
    pub block: Stmt<'ty>,
}

/// Represents a definition (struct, mod, or fun)
///
/// Generate using `Module::get_def_id` or other `Module` declaration functions
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct DefId(u32);

/// The visibility of a symbol relative to its parent module
#[derive(Debug)]
pub enum DefVisibility {
    Public,
    Private,
}

#[derive(Debug)]
pub struct Def<'ty> {
    pub visibility: DefVisibility,
    pub kind: DefKind<'ty>,
    pub external: bool,
}

impl Def<'_> {
    pub fn new(visibility: DefVisibility, kind: DefKind) -> Def {
        Def {
            visibility,
            kind,
            external: false,
        }
    }
    pub fn new_extern(visibility: DefVisibility, kind: DefKind) -> Def {
        Def {
            visibility,
            kind,
            external: true,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum ExternKind {
    Declare,
    Intrinsic,
    VariantConstructor,
    Define,
}

impl Default for ExternKind {
    fn default() -> Self {
        ExternKind::Define
    }
}

#[derive(Debug)]
pub enum DefKind<'ty> {
    Mod {
        symbols: HashMap<String, DefId>,
    },
    Enum {
        ty_params: Vec<String>,
        variants: HashMap<String, Ty<'ty>>,
        symbols: HashMap<String, DefId>,
    },
    Struct {
        ty_params: Vec<String>,
        members: HashMap<String, Ty<'ty>>,
        symbols: HashMap<String, DefId>,
    },
    Fun {
        external: ExternKind,
        ty_params: Vec<String>,
        params: Vec<(String, Ty<'ty>)>,
        return_type: Ty<'ty>,
    },
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Path {
    Terminal(String),
    Namespace(String, Box<Path>),
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Path::*;
        match self {
            Terminal(st) => f.write_str(st),
            Namespace(st, next) => {
                f.write_str(st)?;
                f.write_str("::")?;
                next.fmt(f)
            }
        }
    }
}

impl Path {
    pub fn is_terminal(&self) -> bool {
        use Path::*;
        matches!(self, Terminal(_))
    }

    pub fn tail(&self) -> Option<&Path> {
        use Path::*;
        match self {
            Terminal(_) => None,
            Namespace(_, next) => Some(next),
        }
    }

    pub fn append(&self, end: Path) -> Path {
        use Path::*;
        match self {
            Terminal(name) => Namespace(name.clone(), Box::new(end)),
            Namespace(name, path) => Namespace(name.clone(), Box::new(path.append(end))),
        }
    }

    pub fn push_end(&self, end: String) -> Path {
        use Path::*;
        match self {
            Terminal(name) => Namespace(name.clone(), Box::new(Terminal(end))),
            Namespace(name, path) => Namespace(name.clone(), Box::new(path.push_end(end))),
        }
    }

    pub fn pop_end(&self) -> Option<Path> {
        use Path::*;
        match self {
            Terminal(_) => None,
            Namespace(name, next) if next.is_terminal() => Some(Terminal(name.clone())),
            Namespace(name, path) => {
                Some(Namespace(name.clone(), Box::new(path.pop_end().unwrap())))
            }
        }
    }

    pub fn first(&self) -> &String {
        use Path::*;
        match self {
            Terminal(val) => val,
            Namespace(val, _) => val,
        }
    }

    pub fn end(&self) -> &String {
        use Path::*;
        match self {
            Terminal(val) => val,
            Namespace(_, path) => path.end(),
        }
    }
}

#[derive(Debug)]
pub enum DefineErr {
    AlreadyExists,
    NoModule,
    DeclareOnFun,
}

#[derive(Debug)]
pub struct Module<'ty> {
    next_id: u32,
    expr_id: Cell<u32>,
    defs: HashMap<DefId, Def<'ty>>,
    def_paths: HashMap<Path, DefId>,
    path_defs: HashMap<DefId, Path>,
    expr_tys: RefCell<HashMap<ExprId, Ty<'ty>>>,
    pub functions: HashMap<DefId, Fun<'ty>>,
    pub ty_ctx: TyCtx<'ty>,
    pub const_eval: ConstEvaluator,
}

impl<'ty> Module<'ty> {
    /// Create a new empty module
    pub fn new(ty_ctx: TyCtx<'ty>) -> Module<'ty> {
        Module {
            next_id: 0,
            expr_id: Cell::new(0),
            defs: Default::default(),
            def_paths: Default::default(),
            path_defs: Default::default(),
            expr_tys: Default::default(),
            ty_ctx,
            functions: Default::default(),
            const_eval: ConstEvaluator {},
        }
    }

    pub fn set_ty<E>(&self, expr: E, ty: Ty<'ty>)
    where
        E: Into<ExprId>,
    {
        self.expr_tys.borrow_mut().insert(expr.into(), ty);
    }

    pub fn ty_of<E>(&self, expr: E) -> Ty<'ty>
    where
        E: Into<ExprId>,
    {
        *self
            .expr_tys
            .borrow()
            .get(&expr.into())
            .expect("Internal error")
    }

    pub fn defs_iter<'a>(&'a self) -> std::collections::hash_map::Iter<'a, DefId, Def<'ty>> {
        self.defs.iter()
    }

    pub fn get_def_id(&mut self) -> DefId {
        let id = self.next_id;
        self.next_id += 1;
        DefId(id)
    }

    fn get_expr_id(&self) -> ExprId {
        let id = self.expr_id.get();
        self.expr_id.set(id + 1);
        ExprId(id)
    }

    fn insert_def_path(&mut self, id: DefId, path: Path) {
        self.def_paths.insert(path.clone(), id);
        self.path_defs.insert(id, path);
    }

    pub fn declare_with(
        &mut self,
        path: Path,
        id: DefId,
        def: Def<'ty>,
    ) -> Result<DefId, DefineErr> {
        use DefineErr::*;
        if self.def_paths.contains_key(&path) {
            Err(AlreadyExists)
        } else {
            self.defs.insert(id, def);
            if let Some(head_path) = path.pop_end() {
                match &mut self.get_mut_def_by_path(&head_path).ok_or(NoModule)?.kind {
                    DefKind::Mod { symbols, .. }
                    | DefKind::Struct { symbols, .. }
                    | DefKind::Enum { symbols, .. } => {
                        let end = path.end().clone();
                        assert!(symbols.insert(end, id).is_none(), "symbol already inserted");
                    }
                    _ => {
                        return Err(DeclareOnFun);
                    }
                }
            }
            self.insert_def_path(id, path);
            Ok(id)
        }
    }

    pub fn declare(&mut self, path: Path, def: Def<'ty>) -> Result<DefId, DefineErr> {
        let id = self.get_def_id();
        self.declare_with(path, id, def)
    }

    pub fn get_def_by_id(&self, id: DefId) -> &Def<'ty> {
        self.defs.get(&id).unwrap()
    }

    pub fn get_mut_def_by_id(&mut self, id: DefId) -> &mut Def<'ty> {
        self.defs.get_mut(&id).unwrap()
    }

    pub fn get_def_id_by_path(&self, path: &Path) -> Option<DefId> {
        self.def_paths.get(path).map(Clone::clone)
    }

    pub fn get_def_by_path(&self, path: &Path) -> Option<&Def<'ty>> {
        self.def_paths.get(path).map(|id| self.get_def_by_id(*id))
    }

    pub fn get_mut_def_by_path(&mut self, path: &Path) -> Option<&mut Def<'ty>> {
        Some(self.get_mut_def_by_id(*self.def_paths.get(path)?))
    }

    pub fn get_path_by_def_id(&self, id: DefId) -> &Path {
        self.path_defs.get(&id).unwrap()
    }

    /// Get the module ty context
    pub fn ty_ctx(&self) -> TyCtx<'ty> {
        self.ty_ctx
    }

    /// Get the module's const evaluator
    pub fn const_eval(&self) -> &ConstEvaluator {
        &self.const_eval
    }
}

#[derive(Debug)]
pub struct Stmt<'ty> {
    pub kind: StmtKind<'ty>,
    pub span: Span,
}

impl Stmt<'_> {
    pub fn new(kind: StmtKind, span: Span) -> Stmt {
        Stmt { kind, span }
    }
}

#[derive(Debug, Clone)]
pub enum InlineCParamType {
    Var,
    Type,
}

impl From<&ast::InlineCParamType> for InlineCParamType {
    fn from(ast: &ast::InlineCParamType) -> Self {
        match ast {
            ast::InlineCParamType::Var => InlineCParamType::Var,
            ast::InlineCParamType::Type => InlineCParamType::Type,
        }
    }
}

#[derive(Debug)]
pub enum StmtKind<'ty> {
    InlineC {
        inputs: Vec<(InlineCParamType, String, String)>,
        outputs: Vec<(String, InlineCParamType, String)>,
        code: String,
    },

    If {
        condition: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
        else_block: Option<Box<Stmt<'ty>>>,
    },

    While {
        condition: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
    },

    For {
        initializer: Box<Stmt<'ty>>,
        condition: Box<Expr<'ty>>,
        incrementor: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
    },

    Switch {
        expr: Box<Expr<'ty>>,
        cases: Vec<(Box<Expr<'ty>>, Box<Stmt<'ty>>)>,
        default: Option<Box<Stmt<'ty>>>,
    },

    Labeled(String, Option<Box<Stmt<'ty>>>),

    Block(Vec<Stmt<'ty>>),
    StmtList(Vec<Stmt<'ty>>),
    Return(Option<Box<Expr<'ty>>>),
    Goto(String),

    Expr(Box<Expr<'ty>>),
}

#[derive(Debug, Clone)]
pub struct Expr<'ty> {
    pub kind: ExprKind<'ty>,
    pub span: Span,
    pub id: ExprId,
    /// Field to pass to first arg of function
    pub fun_pass: Option<Box<Expr<'ty>>>,
}

impl<'a, 'ty> From<&'a Expr<'ty>> for ExprId {
    fn from(expr: &'a Expr<'ty>) -> Self {
        expr.id
    }
}

impl<'ty> Expr<'ty> {
    pub fn fun_pass(&self) -> &Option<Box<Expr>> {
        &self.fun_pass
    }

    pub fn fun_pass_mut(&mut self) -> &mut Option<Box<Expr<'ty>>> {
        &mut self.fun_pass
    }

    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn stmt_kind(self) -> StmtKind<'ty> {
        StmtKind::Expr(Box::new(self))
    }

    pub fn stmt(self) -> Stmt<'ty> {
        let span = self.span.clone();
        Stmt::new(self.stmt_kind(), span)
    }
}

#[derive(Debug, Clone)]
pub enum IntegerSpecifier {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),

    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    USize(usize),
    Signed(isize),
    Unsigned(usize),
}

#[derive(Debug, Clone)]
pub enum FloatSpecifier {
    F32(f32),
    F64(f64),
}

#[derive(Debug, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Xor,
    Shl,
    Shr,
    And,
    Or,
    AndAnd,
    OrOr,
    Lt,
    Gt,
    LtEq,
    GtEq,
    EqEq,
    NotEq,
}

impl From<&ast::BinOp> for BinOp {
    fn from(op: &ast::BinOp) -> Self {
        match op {
            ast::BinOp::Add => BinOp::Add,
            ast::BinOp::Sub => BinOp::Sub,
            ast::BinOp::Mul => BinOp::Mul,
            ast::BinOp::Div => BinOp::Div,
            ast::BinOp::Mod => BinOp::Mod,
            ast::BinOp::Xor => BinOp::Xor,
            ast::BinOp::Shl => BinOp::Shl,
            ast::BinOp::Shr => BinOp::Shr,
            ast::BinOp::And => BinOp::And,
            ast::BinOp::Or => BinOp::Or,
            ast::BinOp::AndAnd => BinOp::AndAnd,
            ast::BinOp::OrOr => BinOp::OrOr,
            ast::BinOp::Lt => BinOp::Lt,
            ast::BinOp::Gt => BinOp::Gt,
            ast::BinOp::LtEq => BinOp::LtEq,
            ast::BinOp::GtEq => BinOp::GtEq,
            ast::BinOp::EqEq => BinOp::EqEq,
            ast::BinOp::NotEq => BinOp::NotEq,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AssignOp {
    Eq,
    AddEq,
    SubEq,
    MulEq,
    DivEq,
    ModEq,
    XorEq,
    AndEq,
    OrEq,
}

impl From<&ast::AssignOp> for AssignOp {
    fn from(v: &ast::AssignOp) -> Self {
        match v {
            ast::AssignOp::Eq => AssignOp::Eq,
            ast::AssignOp::AddEq => AssignOp::AddEq,
            ast::AssignOp::SubEq => AssignOp::SubEq,
            ast::AssignOp::MulEq => AssignOp::MulEq,
            ast::AssignOp::DivEq => AssignOp::DivEq,
            ast::AssignOp::ModEq => AssignOp::ModEq,
            ast::AssignOp::XorEq => AssignOp::XorEq,
            ast::AssignOp::AndEq => AssignOp::AndEq,
            ast::AssignOp::OrEq => AssignOp::OrEq,
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Neg,
    LogNot,
    BitNot,
    Deref,
    Ref,
    RefMut,
    Box,
}

impl From<&ast::UnaryOp> for UnaryOp {
    fn from(op: &ast::UnaryOp) -> Self {
        match op {
            ast::UnaryOp::Neg => UnaryOp::Neg,
            ast::UnaryOp::LogNot => UnaryOp::LogNot,
            ast::UnaryOp::BitNot => UnaryOp::BitNot,
            ast::UnaryOp::Deref => UnaryOp::Deref,
            ast::UnaryOp::Ref => UnaryOp::Ref,
            ast::UnaryOp::RefMut => UnaryOp::RefMut,
            ast::UnaryOp::Box => UnaryOp::Box,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind<'ty> {
    Ident(String),
    GlobalIdent(Path, Vec<Ty<'ty>>),
    Integer(IntegerSpecifier),
    Float(FloatSpecifier),
    String(String),
    Bool(bool),

    Null,

    Tuple(Vec<Expr<'ty>>),

    Assign(Box<Expr<'ty>>, AssignOp, Box<Expr<'ty>>),
    Binary(Box<Expr<'ty>>, BinOp, Box<Expr<'ty>>),
    Unary(UnaryOp, Box<Expr<'ty>>),
    Dot(Box<Expr<'ty>>, String),
    Cast(Box<Expr<'ty>>, Ty<'ty>),

    Range(Box<Expr<'ty>>, Box<Expr<'ty>>),
    RangeFrom(Box<Expr<'ty>>),

    Ternary {
        condition: Box<Expr<'ty>>,
        then_expr: Box<Expr<'ty>>,
        else_expr: Box<Expr<'ty>>,
    },

    // expr(index, ...)
    Call {
        expr: Box<Expr<'ty>>,
        arguments: Vec<Expr<'ty>>,
    },

    // expr[index]
    Index {
        expr: Box<Expr<'ty>>,
        index: Box<Expr<'ty>>,
    },

    // [a, b, c, d]
    Array {
        members: Vec<Expr<'ty>>,
    },

    // MyStruct { name: value, name: value }
    Struct {
        ty: Ty<'ty>,
        members: Vec<(String, Box<Expr<'ty>>)>,
    },

    Err,
}
