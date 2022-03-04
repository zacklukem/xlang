//! Handles pretty-printing the IR

use crate::ir::*;
use crate::ty::{AdtType, PointerType, Ty, TyKind};
use std::fmt::{Display, Write};

fn write_type_array<'k, 'a>(
    f: &mut std::fmt::Formatter<'_>,
    arr: &'k [Ty<'a>],
) -> std::fmt::Result {
    for (i, ty) in arr.iter().enumerate() {
        ty.fmt(f)?;
        if i != arr.len() - 1 {
            f.write_str(", ")?;
        }
    }
    Ok(())
}

pub fn type_array_str(arr: &[Ty<'_>]) -> String {
    let mut out = String::new();
    for (i, ty) in arr.iter().enumerate() {
        let ty = format!("{ty}");
        out += &ty[..];
        if i != arr.len() - 1 {
            out += ", ";
        }
    }
    out
}

impl Display for Ty<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0 .0.fmt(f)
    }
}

impl Display for TyKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyKind::Param(p) => f.write_str(p),
            TyKind::Primitive(pt) => write!(f, "{pt}"),
            TyKind::Adt(AdtType {
                path, ty_params, ..
            }) => {
                write!(f, "{}", path)?;
                if !ty_params.is_empty() {
                    f.write_str("<")?;
                    write_type_array(f, ty_params)?;
                    f.write_str(">")?;
                }
                Ok(())
            }
            TyKind::Pointer(PointerType::Star, ty) => write!(f, "*{ty}"),
            TyKind::Pointer(PointerType::StarMut, ty) => write!(f, "*mut {ty}"),
            TyKind::Tuple(tys) => {
                f.write_str("(")?;
                write_type_array(f, tys)?;
                f.write_str(")")
            }
            TyKind::Fun(tys, ret) => {
                f.write_str("(")?;
                write_type_array(f, tys)?;
                write!(f, ") -> {ret}")
            }
            TyKind::SizedArray(size, ty) => write!(f, "[{size}]{ty}"),
            TyKind::UnsizedArray(ty) => write!(f, "[]{ty}"),
            TyKind::Range(ty) => write!(f, "<RANGE {ty}>"),
            TyKind::Err => write!(f, "<ERR_TYPE>"),
            TyKind::TyVar(id) => write!(f, "?{}", id.to_human_readable()),
        }
    }
}

impl std::fmt::Debug for Fun<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "fun {}", self.db_name)?;

        for (name, ty) in &self.variable_defs {
            writeln!(f, "let {name}: {ty}")?;
        }

        let block_string = format!("{}", self.block);
        let mut level = 0;
        let mut last = '\0';

        for c in block_string.chars() {
            if c == '{' {
                level += 1;
            } else if c == '}' {
                level -= 1;
            }
            if last == '\n' {
                for _ in 0..level {
                    f.write_str("    ")?;
                }
            }
            f.write_char(c)?;
            last = c;
        }
        f.write_char('\n')
    }
}

impl Display for Stmt<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

impl Display for StmtKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StmtKind::If {
                condition,
                block,
                else_block: Some(else_block),
            } => write!(f, "if {condition} {block} else {else_block}"),

            StmtKind::If {
                condition,
                block,
                else_block: None,
            } => write!(f, "if {condition} {block}"),

            StmtKind::While { condition, block } => write!(f, "while {condition} {block}"),

            StmtKind::For {
                initializer,
                condition,
                incrementor,
                block,
            } => write!(f, "for {initializer}; {condition}; {incrementor} {block}"),

            StmtKind::Labeled(label, Some(stmt)) => write!(f, "{label}:\n{stmt}"),
            StmtKind::Labeled(label, None) => writeln!(f, "{label}:"),

            StmtKind::Block(stmts) => {
                f.write_str("{\n")?;
                for stmt in stmts {
                    stmt.fmt(f)?;
                    f.write_str("\n")?;
                }
                f.write_str("}")
            }

            StmtKind::StmtList(stmts) => {
                f.write_str("/* Begin StmtList */\n")?;
                for stmt in stmts {
                    stmt.fmt(f)?;
                    f.write_str("\n")?;
                }
                f.write_str("/* End StmtList */\n")
            }
            StmtKind::Return(Some(val)) => write!(f, "return {val};"),
            StmtKind::Return(None) => write!(f, "return;"),
            StmtKind::Goto(label) => write!(f, "goto {label};"),
            StmtKind::Expr(expr) => write!(f, "{expr};"),
            StmtKind::Switch {
                expr,
                cases,
                default,
            } => {
                f.write_str("switch ")?;
                expr.fmt(f)?;
                f.write_str("{")?;
                for (det, stmts) in cases {
                    f.write_str("\n| ")?;
                    det.fmt(f)?;
                    f.write_str(" -> ")?;
                    stmts.fmt(f)?;
                }
                if let Some(stmts) = default {
                    f.write_str("\n| _ ->")?;
                    stmts.fmt(f)?;
                }
                f.write_str("}}")
            }
            StmtKind::InlineC { code, .. } => {
                write!(f, "[INLINE_C: {code}]")
            }
        }
    }
}

impl Display for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // write!(f, "{}<{}>", self.kind(), self.ty())
        write!(f, "{}", self.kind())
    }
}

impl Display for IntegerSpecifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntegerSpecifier::I8(val) => write!(f, "{val}"),
            IntegerSpecifier::I16(val) => write!(f, "{val}"),
            IntegerSpecifier::I32(val) => write!(f, "{val}"),
            IntegerSpecifier::I64(val) => write!(f, "{val}"),
            IntegerSpecifier::U8(val) => write!(f, "{val}"),
            IntegerSpecifier::U16(val) => write!(f, "{val}"),
            IntegerSpecifier::U32(val) => write!(f, "{val}"),
            IntegerSpecifier::U64(val) => write!(f, "{val}"),
            IntegerSpecifier::USize(val) => write!(f, "{val}"),
            IntegerSpecifier::Signed(val) => write!(f, "{val}"),
            IntegerSpecifier::Unsigned(val) => write!(f, "{val}"),
        }
    }
}

impl Display for FloatSpecifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FloatSpecifier::F32(val) => write!(f, "{val}"),
            FloatSpecifier::F64(val) => write!(f, "{val}"),
        }
    }
}

impl Display for AssignOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = match self {
            AssignOp::Eq => "=",
            AssignOp::AddEq => "+=",
            AssignOp::SubEq => "-=",
            AssignOp::MulEq => "*=",
            AssignOp::DivEq => "/=",
            AssignOp::ModEq => "%=",
            AssignOp::XorEq => "^=",
            AssignOp::AndEq => "&=",
            AssignOp::OrEq => "|=",
        };
        f.write_str(v)
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Xor => "^",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::And => "&",
            BinOp::Or => "|",
            BinOp::AndAnd => "&&",
            BinOp::OrOr => "||",
            BinOp::Lt => "<",
            BinOp::Gt => ">",
            BinOp::LtEq => "<=",
            BinOp::GtEq => ">=",
            BinOp::EqEq => "==",
            BinOp::NotEq => "!=",
        };
        f.write_str(v)
    }
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = match self {
            UnaryOp::Neg => "-",
            UnaryOp::LogNot => "!",
            UnaryOp::BitNot => "~",
            UnaryOp::Deref => "*",
            UnaryOp::Ref => "&",
            UnaryOp::RefMut => "&mut ",
            UnaryOp::Box => "box ",
        };
        f.write_str(v)
    }
}

fn write_expr_array(f: &mut std::fmt::Formatter<'_>, arr: &[Expr]) -> std::fmt::Result {
    for (i, ty) in arr.iter().enumerate() {
        ty.fmt(f)?;
        if i != arr.len() - 1 {
            f.write_str(", ")?;
        }
    }
    Ok(())
}

impl Display for ExprKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprKind::Null => f.write_str("null"),
            ExprKind::Ident(name) => f.write_str(name),

            ExprKind::GlobalIdent(val, generics) => {
                val.fmt(f)?;
                if !generics.is_empty() {
                    f.write_str("<")?;
                    write_type_array(f, generics)?;
                    f.write_str(">")?;
                }
                Ok(())
            }
            ExprKind::Integer(val) => val.fmt(f),
            ExprKind::Float(val) => val.fmt(f),
            ExprKind::String(string) => f.write_str(string),
            ExprKind::Bool(true) => f.write_str("true"),
            ExprKind::Bool(false) => f.write_str("false"),
            ExprKind::Tuple(exprs) => {
                f.write_str("(")?;
                write_expr_array(f, exprs)?;
                f.write_str(")")
            }
            ExprKind::Assign(lhs, op, rhs) => write!(f, "{lhs} {op} {rhs}"),
            ExprKind::Binary(lhs, op, rhs) => write!(f, "({lhs} {op} {rhs})"),
            ExprKind::Unary(op, rhs) => write!(f, "({op}{rhs})"),
            ExprKind::Dot(lhs, rhs) => write!(f, "{lhs}.{rhs}"),
            ExprKind::Cast(lhs, ty) => write!(f, "({lhs} as {ty})"),
            ExprKind::Range(low, high) => write!(f, "({low}..{high})"),
            ExprKind::RangeFrom(low) => write!(f, "({low}..)"),
            ExprKind::Ternary {
                condition,
                then_expr,
                else_expr,
            } => write!(f, "(if {condition} then {then_expr} else {else_expr})",),
            ExprKind::Call { expr, arguments } => {
                expr.fmt(f)?;
                f.write_str("(")?;
                write_expr_array(f, arguments)?;
                f.write_str(")")
            }
            ExprKind::Index { expr, index } => write!(f, "{expr}[{index}]"),
            ExprKind::Array { members } => {
                f.write_str("[")?;
                write_expr_array(f, members)?;
                f.write_str("]")
            }
            ExprKind::Struct { ty, members, .. } => {
                ty.fmt(f)?;
                f.write_str(" of {")?;
                for (i, (name, val)) in members.iter().enumerate() {
                    write!(f, "{name}: {val}")?;
                    if i != members.len() - 1 {
                        f.write_str(", ")?;
                    }
                }
                f.write_str("}")
            }
            ExprKind::Err => f.write_str("<ERR_EXPR>"),
        }
    }
}
