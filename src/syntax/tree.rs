use crate::syntax::{RangeEnd, Token};
use crate::ty::{Type, TypeContext};
use std::cell::Cell;
use std::fmt;
use typed_arena::Arena;

#[derive(Debug)]
pub struct Expr<'pcx, 'tcx> {
    kind: ExprKind<'pcx, 'tcx>,
    // The type of expression is determined in later phase.
    ty: Cell<Option<&'tcx Type<'tcx>>>,
    // comments followed by this token.
    comments: Vec<String>,
}

impl<'pcx, 'tcx> Expr<'pcx, 'tcx> {
    pub fn new(kind: ExprKind<'pcx, 'tcx>) -> Self {
        Self {
            kind,
            ty: Cell::new(None),
            comments: vec![],
        }
    }

    pub fn kind(&self) -> &ExprKind<'pcx, 'tcx> {
        &self.kind
    }

    pub fn ty(&self) -> Option<&'tcx Type<'tcx>> {
        self.ty.get()
    }

    pub fn assign_ty(&self, ty: &'tcx Type<'tcx>) {
        self.ty.set(Some(ty))
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
    }

    pub fn append_comments_from(&mut self, token: &Token) {
        for comment in token.comments() {
            self.comments.push(comment.to_string());
        }
    }
}

#[derive(Debug)]
pub enum ExprKind<'pcx, 'tcx> {
    Integer(i64),
    Boolean(bool),
    String(String),
    Var(String),

    // unary operators
    Minus(&'pcx Expr<'pcx, 'tcx>),

    // binary operators
    Add(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Sub(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Mul(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Div(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Eq(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Ne(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Le(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Ge(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Lt(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Gt(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    And(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),
    Or(&'pcx Expr<'pcx, 'tcx>, &'pcx Expr<'pcx, 'tcx>),

    Call(String, Vec<&'pcx Expr<'pcx, 'tcx>>),
    Let {
        name: String,
        rhs: &'pcx Expr<'pcx, 'tcx>,
        then: &'pcx Expr<'pcx, 'tcx>,
    },
    Fn(Function<'pcx, 'tcx>),
    Case {
        head: &'pcx Expr<'pcx, 'tcx>,
        arms: Vec<CaseArm<'pcx, 'tcx>>,
        else_body: Option<&'pcx Expr<'pcx, 'tcx>>,
    },

    // Built-in functions
    Puts(Vec<&'pcx Expr<'pcx, 'tcx>>),
}

#[derive(Debug)]
pub struct Function<'pcx, 'tcx> {
    name: String,
    params: Vec<Parameter<'tcx>>,
    body: &'pcx Expr<'pcx, 'tcx>,
    then: &'pcx Expr<'pcx, 'tcx>,
}

impl<'pcx, 'tcx> Function<'pcx, 'tcx> {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn params(&self) -> &[Parameter] {
        &self.params
    }

    pub fn body(&self) -> &Expr<'pcx, 'tcx> {
        self.body
    }

    pub fn then(&self) -> &Expr<'pcx, 'tcx> {
        self.then
    }
}

/// Formal parameter for a function
#[derive(Debug)]
pub struct Parameter<'tcx> {
    name: String,
    ty: &'tcx Type<'tcx>,
}

impl<'tcx> Parameter<'tcx> {
    pub fn new(name: &str, ty: &'tcx Type<'tcx>) -> Self {
        Self {
            name: name.to_string(),
            ty,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }
}

#[derive(Debug)]
pub struct CaseArm<'pcx, 'tcx> {
    pattern: &'pcx Pattern<'pcx, 'tcx>,
    body: &'pcx Expr<'pcx, 'tcx>,
    comments: Vec<String>,
}

impl<'pcx, 'tcx> CaseArm<'pcx, 'tcx> {
    pub fn new(pattern: &'pcx Pattern<'pcx, 'tcx>, body: &'pcx Expr<'pcx, 'tcx>) -> Self {
        Self {
            pattern,
            body,
            comments: vec![],
        }
    }

    pub fn pattern(&self) -> &'pcx Pattern<'pcx, 'tcx> {
        self.pattern
    }

    pub fn body(&self) -> &'pcx Expr<'pcx, 'tcx> {
        self.body
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
    }

    pub fn append_comments_from(&mut self, token: &Token) {
        for comment in token.comments() {
            self.comments.push(comment.to_string());
        }
    }
}

#[derive(Debug)]
pub struct Pattern<'pcx, 'tcx> {
    kind: PatternKind<'pcx, 'pcx>,
    ty: &'tcx Type<'tcx>,
    comments: Vec<String>,
}

impl<'pcx, 'tcx> Pattern<'pcx, 'tcx> {
    pub fn new(kind: PatternKind<'pcx, 'tcx>, ty: &'tcx Type<'tcx>) -> Self {
        Self {
            kind,
            ty,
            comments: vec![],
        }
    }

    pub fn kind(&self) -> &PatternKind<'pcx, 'pcx> {
        &self.kind
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
    }

    pub fn append_comments_from(&mut self, token: &Token) {
        for comment in token.comments() {
            self.comments.push(comment.to_string());
        }
    }
}

#[derive(Debug)]
pub enum PatternKind<'pcx, 'tcx> {
    Integer(i64),
    Boolean(bool),
    String(String),
    Range { lo: i64, hi: i64, end: RangeEnd },
    Or(&'pcx Pattern<'pcx, 'tcx>, &'pcx Pattern<'pcx, 'tcx>),
    Wildcard(&'tcx Type<'tcx>),
}

impl fmt::Display for PatternKind<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternKind::Integer(n) => write!(f, "{}", n),
            PatternKind::Boolean(b) => write!(f, "{}", b),
            PatternKind::String(s) => write!(f, "\"{}\"", s.escape_default().collect::<String>()),
            PatternKind::Range { lo, hi, end } => {
                if *lo == i64::MIN {
                    write!(f, "int64::MIN")?;
                } else {
                    write!(f, "{}", lo)?;
                }

                write!(f, "{}", end)?;

                if *hi == i64::MAX {
                    write!(f, "int64::MAX")
                } else {
                    write!(f, "{}", hi)
                }
            }
            PatternKind::Or(_, _) => todo!(),
            PatternKind::Wildcard(_) => write!(f, "_"),
        }
    }
}

pub struct Parser<'pcx, 'tcx> {
    pub tcx: TypeContext<'tcx>,
    pub expr_arena: &'pcx Arena<Expr<'pcx, 'tcx>>,
    pub pat_arena: &'pcx Arena<Pattern<'pcx, 'tcx>>,
}

#[allow(dead_code)]
impl<'pcx, 'tcx> Parser<'pcx, 'tcx> {
    pub fn new(
        tcx: TypeContext<'tcx>,
        expr_arena: &'pcx Arena<Expr<'pcx, 'tcx>>,
        pat_arena: &'pcx Arena<Pattern<'pcx, 'tcx>>,
    ) -> Self {
        Self {
            tcx,
            expr_arena,
            pat_arena,
        }
    }

    pub fn parse(&self, _tokens: &[Token]) -> Result<&'pcx Expr<'pcx, 'tcx>, Vec<String>> {
        Err(vec![])
    }

    // --- Misc

    fn alloc_expr(&self, expr: Expr<'pcx, 'tcx>) -> &'pcx Expr<'pcx, 'tcx> {
        // Make mutable reference to immutable to suppress compiler error for mutability mismatch.
        self.expr_arena.alloc(expr)
    }

    fn alloc_pat(&self, pat: Pattern<'pcx, 'tcx>) -> &'pcx Pattern<'pcx, 'tcx> {
        // Make mutable reference to immutable to suppress compiler error for mutability mismatch.
        self.pat_arena.alloc(pat)
    }
}
