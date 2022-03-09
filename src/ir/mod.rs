//! The IR data structures

pub mod ir_build;
pub mod ir_display;

use crate::ast::{self, Span};
use crate::const_eval::ConstEvaluator;
use crate::generics::replace_generics;
use crate::ty::{Ty, TyCtx, TyKind};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;

/// An id that uniquely identifies each expression. This is used to give types
/// to IR expressions. An ExprId is generated when an expression is created
/// using the [`Module::mk_expr`] function.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ExprId(u32);

/// A high level function body in the IR.  This contains the [`DefId`]
/// of the function, a list of function-scoped variable definitions and an ir
/// [`Stmt`] block for the actual code.
pub struct Fun<'ty> {
    /// The [`DefId`] of the function
    pub def_id: DefId,
    /// Used for debugging.
    pub db_name: String,
    /// The variable definitions for this function. Since variables in the IR
    /// are all function-scoped, there is only one list of variable definitions
    /// per function which are initialized in the function body.
    pub variable_defs: Vec<(String, Ty<'ty>)>,
    /// The function body
    pub block: Stmt<'ty>,
}

/// A definition (struct, mod, or fun)
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

/// A top-level definition such as a structure, enum or function.
#[derive(Debug)]
pub struct Def<'ty> {
    /// The visibility of the definition (public or private)
    pub visibility: DefVisibility,
    /// The actual data
    pub kind: DefKind<'ty>,
    /// If this definition is external (applies only to functions)
    pub external: bool,
}

impl<'ty> Def<'ty> {
    pub fn new(visibility: DefVisibility, kind: DefKind) -> Def {
        Def {
            visibility,
            kind,
            external: false,
        }
    }

    /// Create an external def
    pub fn new_extern(visibility: DefVisibility, kind: DefKind) -> Def {
        Def {
            visibility,
            kind,
            external: true,
        }
    }

    /// Get the fields from a structure if this is a structure, otherwise return [`None`].
    pub fn get_struct_fields(
        &self,
    ) -> Option<(
        &Vec<String>,
        &HashMap<String, Ty<'ty>>,
        &HashMap<String, DefId>,
    )> {
        if let DefKind::Struct {
            ty_params,
            members,
            symbols,
        } = &self.kind
        {
            Some((ty_params, members, symbols))
        } else {
            None
        }
    }

    /// If this is a function, return the type of the function as a function pointer
    /// otherwise return [`None`]
    pub fn fn_type(&self, tcx: TyCtx<'ty>, generics: &[Ty<'ty>]) -> Option<Ty<'ty>> {
        if let DefKind::Fun {
            ty_params,
            return_type,
            params,
            ..
        } = &self.kind
        {
            assert_eq!(ty_params.len(), generics.len());
            let generics = ty_params
                .iter()
                .cloned()
                .zip(generics.iter().copied())
                .collect::<Vec<_>>();
            let return_type = replace_generics(tcx, *return_type, &generics);
            let params = params
                .iter()
                .map(|(_, param)| replace_generics(tcx, *param, &generics))
                .collect::<Vec<_>>();

            Some(tcx.int(TyKind::Fun(params, return_type)))
        } else {
            None
        }
    }

    pub fn kind(&self) -> &DefKind<'ty> {
        &self.kind
    }
}

/// The kind of extern function
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum ExternKind {
    /// External functions which will be declared in the output C
    /// header, but not defined
    Declare,

    /// Special functions such as `sizeof` which will be inlined by
    /// the compiler
    Intrinsic,

    /// Constructors for variants which will be declared in the output
    /// C header but contain no IR for the body as the body is generated in the
    /// codegen stage.
    VariantConstructor,

    /// This represents non-external functions which will be defined
    Define,
}

impl Default for ExternKind {
    fn default() -> Self {
        ExternKind::Define
    }
}

#[derive(Debug)]
pub enum DefKind<'ty> {
    /// A module (namespace).  This is just a list of the symbols in a module
    /// used to enumerate all members in a module.
    Mod { symbols: HashMap<String, DefId> },

    /// An enum (variant) definition
    Enum {
        ty_params: Vec<String>,
        variants: HashMap<String, Ty<'ty>>,
        symbols: HashMap<String, DefId>,
    },

    /// A struct definition
    Struct {
        /// The named type parameters in the struct definition
        ty_params: Vec<String>,

        /// The fields in a structure
        members: HashMap<String, Ty<'ty>>,

        /// The functions in this structure
        ///
        /// Because structures also act as modules and can contain functions,
        /// we need to keep a list of these.
        symbols: HashMap<String, DefId>,
    },

    /// A function definition
    Fun {
        external: ExternKind,
        ty_params: Vec<String>,
        params: Vec<(String, Ty<'ty>)>,
        return_type: Ty<'ty>,
    },
}

/// A path identifies a definition by its parent modules.
///
/// Paths stored in the IR should be fully qualified
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
    /// Create a path from a list of segments.  The list of segments must not be
    /// empty.
    ///
    /// ```
    /// use Path::*;
    /// let path = Path::from_segments(&["first", "second", "third"]);
    /// assert_eq!(
    ///     path,
    ///     Namespace(
    ///         "first".to_string(),
    ///         Box::new(Namespace(
    ///             "second".to_string(),
    ///             Box::new(Terminal("third".to_string())),
    ///         )),
    ///     ),
    /// );
    /// ```
    pub fn from_segments(segments: &[&str]) -> Path {
        assert!(!segments.is_empty());
        let mut iter = segments.iter().rev();
        let mut out = Path::Terminal(iter.next().unwrap().to_string());
        for segment in iter {
            out = Path::Namespace(segment.to_string(), Box::new(out));
        }
        out
    }

    /// Returns true if this is a terminal path (it has no parent)
    pub fn is_terminal(&self) -> bool {
        use Path::*;
        matches!(self, Terminal(_))
    }

    /// Get the tail of a path segment (pops the first element)
    ///
    /// Returns [`None`] if the path has only one segment
    ///
    /// ```
    /// assert_eq!(
    ///     Path::from_segments(&["first", "second", "third"]).tail(),
    ///     Some(&Path::from_segments(&["second", "third"])),
    /// );
    /// assert_eq!(
    ///     Path::from_segments(&["first"]).tail(),
    ///     None,
    /// );
    /// ```
    pub fn tail(&self) -> Option<&Path> {
        use Path::*;
        match self {
            Terminal(_) => None,
            Namespace(_, next) => Some(next),
        }
    }

    /// Append a path to the end of another
    ///
    /// ```
    /// assert_eq!(
    ///     Path::from_segments(&["a", "b", "c", "d"]),
    ///     Path::from_segments(&["a", "b"]).append(
    ///         Path::from_segments(&["c", "d"]),
    ///     ),
    /// );
    /// ```
    pub fn append(&self, end: Path) -> Path {
        use Path::*;
        match self {
            Terminal(name) => Namespace(name.clone(), Box::new(end)),
            Namespace(name, path) => Namespace(name.clone(), Box::new(path.append(end))),
        }
    }

    /// Create a new path with the given segment at the end
    ///
    /// ```
    /// assert_eq!(
    ///     Path::from_segments(&["a", "b"]),
    ///     Path::from_segments(&["a"]).push_end("b".to_string());
    /// );
    /// ```
    pub fn push_end(&self, end: String) -> Path {
        use Path::*;
        match self {
            Terminal(name) => Namespace(name.clone(), Box::new(Terminal(end))),
            Namespace(name, path) => Namespace(name.clone(), Box::new(path.push_end(end))),
        }
    }

    /// Pop the end from a path.  Returns [`None`] if the path has only one
    /// segment.
    ///
    /// ```
    /// assert_eq!(
    ///     Path::from_segments(&["a", "b"]).pop_end(),
    ///     Some(Path::from_segments(&["a"])),
    /// );
    /// assert_eq!(
    ///     Path::from_segments(&["a"]).pop_end(),
    ///     None,
    /// );
    /// ```
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

    /// Gets the first segment of a path
    ///
    /// ```
    /// assert_eq!(
    ///     Path::from_segments(&["a", "b"]).first(),
    ///     "a".to_string,
    /// );
    /// ```
    pub fn first(&self) -> &String {
        use Path::*;
        match self {
            Terminal(val) => val,
            Namespace(val, _) => val,
        }
    }

    /// Gets the last segment of a path
    ///
    /// ```
    /// assert_eq!(
    ///     Path::from_segments(&["a", "b"]).first(),
    ///     "b".to_string,
    /// );
    /// ```
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

/// The overall IR module.  This is contains all the definitions for a program,
/// the types of all expressions, and all function bodies.
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

    /// Set the type of an expression
    pub fn set_ty<E>(&self, expr: E, ty: Ty<'ty>)
    where
        E: Into<ExprId>,
    {
        self.expr_tys.borrow_mut().insert(expr.into(), ty);
    }

    /// Get the type of an expression.  Panics if the expression has no type
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

    /// Get an iterator over all the defs in this module
    pub fn defs_iter<'a>(&'a self) -> std::collections::hash_map::Iter<'a, DefId, Def<'ty>> {
        self.defs.iter()
    }

    /// Get a new unique [`DefId`]
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

    /// Declare a new definition with the given path and [`DefId`]
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

    /// Declare a new definition with the given path and generate a new unique
    /// [`DefId`]
    pub fn declare(&mut self, path: Path, def: Def<'ty>) -> Result<DefId, DefineErr> {
        let id = self.get_def_id();
        self.declare_with(path, id, def)
    }

    /// Get a definition by its [`DefId`]
    pub fn get_def_by_id(&self, id: DefId) -> &Def<'ty> {
        self.defs.get(&id).unwrap()
    }

    /// Get a mutable reference to a definition by its [`DefId`]
    pub fn get_mut_def_by_id(&mut self, id: DefId) -> &mut Def<'ty> {
        self.defs.get_mut(&id).unwrap()
    }

    /// Get the [`DefId`] that corresponds to the given path
    pub fn get_def_id_by_path(&self, path: &Path) -> Option<DefId> {
        self.def_paths.get(path).map(Clone::clone)
    }

    /// Get a definition by its path
    pub fn get_def_by_path(&self, path: &Path) -> Option<&Def<'ty>> {
        self.def_paths.get(path).map(|id| self.get_def_by_id(*id))
    }

    /// Get a mutable reference to a definition by its path
    pub fn get_mut_def_by_path(&mut self, path: &Path) -> Option<&mut Def<'ty>> {
        Some(self.get_mut_def_by_id(*self.def_paths.get(path)?))
    }

    /// Get the path that corresponds to a given [`DefId`]
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

/// Represents a statement
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

/// The type of a symbol passed to an inline C statement
#[derive(Debug, Clone, Copy)]
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
    /// Inline c code
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
        cases: Vec<(Expr<'ty>, Stmt<'ty>)>,
        default: Option<Box<Stmt<'ty>>>,
    },

    /// A labeled statement or a label at the end of a block
    Labeled(String, Option<Box<Stmt<'ty>>>),

    Block(Vec<Stmt<'ty>>),
    /// A list of statements that are not put in any particular block
    StmtList(Vec<Stmt<'ty>>),
    Return(Option<Box<Expr<'ty>>>),
    Goto(String),

    Expr(Box<Expr<'ty>>),
}

/// An expression
#[derive(Debug, Clone)]
pub struct Expr<'ty> {
    pub kind: ExprKind<'ty>,
    pub span: Span,
    pub id: ExprId,
}

impl<'a, 'ty> From<&'a Expr<'ty>> for ExprId {
    fn from(expr: &'a Expr<'ty>) -> Self {
        expr.id
    }
}

impl<'ty> Expr<'ty> {
    /// Coerce an reference expression to the given reference level
    ///
    /// For example, an expression `expr` of type `****T` called with `coerce_ref(.., 3)`
    /// becomes an expression `*expr` with type `***T`
    pub fn coerce_ref(mut self, md: &Module<'ty>, level: u8) -> Expr<'ty> {
        let ref_level = md.ty_of(&self).ref_level();
        // Number of refs/derefs (-2 means deref twice), (+2 means ref twice)
        let motion = level as i8 - ref_level as i8;
        if motion == 0 {
            self
        } else if motion < 0 {
            for _ in 0..(-motion as usize) {
                let span = self.span.clone();
                let ty = md.ty_of(&self).deref_ty().unwrap();
                self = md.mk_expr(ExprKind::Unary(UnaryOp::Deref, Box::new(self)), span, ty);
            }
            self
        } else {
            for _ in 0..(motion as usize) {
                let span = self.span.clone();
                let ty = md.ty_of(&self).ptr(md.ty_ctx());
                self = md.mk_expr(ExprKind::Unary(UnaryOp::Ref, Box::new(self)), span, ty);
            }
            self
        }
    }

    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    /// Turn this expression into an expr stmt without wrapping in stmt
    pub fn stmt_kind(self) -> StmtKind<'ty> {
        StmtKind::Expr(Box::new(self))
    }

    /// Turn this expression into an expr stmt
    pub fn stmt(self) -> Stmt<'ty> {
        let span = self.span.clone();
        Stmt::new(self.stmt_kind(), span)
    }
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug, Clone, Copy)]
pub enum FloatSpecifier {
    F32(f32),
    F64(f64),
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug, Clone, Copy)]
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
    /// Gets the discriminant of an enum value
    ///
    /// `Discriminant(expr)` generates something like `expr.kind`
    Discriminant(Box<Expr<'ty>>),

    /// Get the value of a particular variant
    ///
    /// Used for patterns to get the data out of an enum
    /// `GetVariant(expr, "VariantName")` compiles to something like
    /// `expr.VariantName`.
    GetVariant(Box<Expr<'ty>>, String),

    /// A constant value which is the value of the discriminant of an enum at the
    /// given path.  For example, `DiscriminantValue(module::Enum::Variant)`
    /// compiles to something like `module_Enum_Variant_k`
    DiscriminantValue(Path),

    /// Get a value from a tuple
    ///
    /// `TupleValue(expr, 0)` compiles to something like `expr._0`
    TupleValue(Box<Expr<'ty>>, u8),

    /// This represents a function-scoped variable
    Ident(String),
    /// This represents a globally scoped path to a definition with type params
    GlobalIdent(Path, Vec<Ty<'ty>>),

    /// An integer literal
    Integer(IntegerSpecifier),
    /// A float literal
    Float(FloatSpecifier),
    /// A string literal
    String(String),
    /// A boolean literal
    Bool(bool),

    /// A null literal
    Null,

    /// A tuple constructor
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
