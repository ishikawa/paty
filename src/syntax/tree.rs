use crate::syntax::{RangeEnd, Token, TokenKind};
use crate::ty::{Type, TypeContext};
use std::cell::Cell;
use std::fmt;
use std::iter::Peekable;
use std::slice;
use thiserror::Error;
use typed_arena::Arena;

#[derive(Error, Debug)]
pub enum ParseError<'t> {
    // Token iterator was not consumed, so you can safely retry to parse another node.
    #[error("expected {expected}, but was {actual}")]
    UnexpectedLookaheadToken { expected: String, actual: &'t Token },
    #[error("expected {expected}, but was {actual}")]
    UnexpectedToken { expected: String, actual: &'t Token },
    #[error("Premature end of file")]
    PrematureEnd,
}

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

pub type ParseResult<'t, 'pcx, 'tcx> = Result<&'pcx Expr<'pcx, 'tcx>, ParseError<'t>>;

type TokenIterator<'t> = Peekable<slice::Iter<'t, Token>>;

#[allow(dead_code)]
impl<'t, 'pcx, 'tcx> Parser<'pcx, 'tcx> {
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

    pub fn parse(&self, tokens: &'t [Token]) -> ParseResult<'t, 'pcx, 'tcx> {
        let mut it = tokens.iter().peekable();

        self.expr(&mut it)
    }

    // --- Parser
    fn expr(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'pcx, 'tcx> {
        self.atom(it)
    }

    fn atom(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'pcx, 'tcx> {
        let token = self.peek_token(it)?;
        let kind = match token.kind() {
            TokenKind::Integer(n) => {
                it.next();

                let i = n.parse().unwrap();
                ExprKind::Integer(i)
            }
            TokenKind::Identifier(name) => {
                it.next();

                // call?
                if self.match_token(it, TokenKind::Operator('('))? {
                    let args = self.parse_elements(it, Self::expr)?;
                    ExprKind::Call(name.clone(), args)
                } else {
                    ExprKind::Var(name.clone())
                }
            }
            TokenKind::Puts => {
                it.next();

                let args = self.parse_elements(it, Self::expr)?;
                ExprKind::Puts(args)
            }
            TokenKind::LiteralString(s) => {
                it.next();
                ExprKind::String(s.clone())
            }
            TokenKind::True => {
                it.next();
                ExprKind::Boolean(true)
            }
            TokenKind::False => {
                it.next();
                ExprKind::Boolean(false)
            }
            TokenKind::Operator('(') => {
                it.next();
                let expr = self.expr(it)?;
                self.expect_token(it, TokenKind::Operator(')'))?;

                return Ok(expr);
            }
            _ => {
                return Err(ParseError::UnexpectedLookaheadToken {
                    expected: "atom".to_string(),
                    actual: token,
                });
            }
        };

        Ok(self.alloc_expr(kind, token))
    }

    // --- Misc
    fn parse_elements(
        &self,
        it: &mut TokenIterator<'t>,
        parser: fn(&Self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'pcx, 'tcx>,
    ) -> Result<Vec<&'pcx Expr<'pcx, 'tcx>>, ParseError<'t>> {
        let mut args = vec![];

        self.expect_token(it, TokenKind::Operator('('))?;
        {
            while let Some(arg) = self.lookahead(parser(self, it))? {
                args.push(arg);

                // trailing comma can be omitted
                if self.match_token(it, TokenKind::Operator(','))? {
                    it.next();
                } else if !self.match_token(it, TokenKind::Operator(')'))? {
                    let actual = self.peek_token(it)?;
                    return Err(ParseError::UnexpectedToken {
                        expected: "')' or ','".to_string(),
                        actual,
                    });
                }
            }
        }
        self.expect_token(it, TokenKind::Operator(')'))?;
        Ok(args)
    }

    fn peek_token(&self, it: &mut TokenIterator<'t>) -> Result<&'t Token, ParseError<'t>> {
        Ok(it.peek().ok_or(ParseError::PrematureEnd)?)
    }

    fn ensure_lookahead(
        &self,
        it: &mut TokenIterator<'t>,
        kind: TokenKind,
    ) -> Result<&'t Token, ParseError<'t>> {
        let token = self.peek_token(it)?;

        if *token.kind() == kind {
            Ok(it.next().unwrap())
        } else {
            Err(ParseError::UnexpectedLookaheadToken {
                expected: kind.to_string(),
                actual: token,
            })
        }
    }

    fn expect_token(
        &self,
        it: &mut TokenIterator<'t>,
        kind: TokenKind,
    ) -> Result<&'t Token, ParseError<'t>> {
        let token = self.peek_token(it)?;

        if *token.kind() == kind {
            Ok(it.next().unwrap())
        } else {
            Err(ParseError::UnexpectedToken {
                expected: kind.to_string(),
                actual: token,
            })
        }
    }

    fn match_token(
        &self,
        it: &mut TokenIterator<'t>,
        kind: TokenKind,
    ) -> Result<bool, ParseError<'t>> {
        let token = self.peek_token(it)?;
        Ok(*token.kind() == kind)
    }

    fn lookahead(
        &self,
        r: ParseResult<'t, 'pcx, 'tcx>,
    ) -> Result<Option<&'pcx Expr<'pcx, 'tcx>>, ParseError<'t>> {
        match r {
            Ok(expr) => Ok(Some(expr)),
            Err(ParseError::UnexpectedLookaheadToken { .. }) => Ok(None),
            Err(err) => Err(err),
        }
    }

    fn alloc_expr(&self, kind: ExprKind<'pcx, 'tcx>, token: &Token) -> &'pcx Expr<'pcx, 'tcx> {
        let mut expr = Expr::new(kind);
        expr.append_comments_from(token);

        // Make mutable reference to immutable to suppress compiler error for mutability mismatch.
        self.expr_arena.alloc(expr)
    }

    fn alloc_pat(&self, pat: Pattern<'pcx, 'tcx>) -> &'pcx Pattern<'pcx, 'tcx> {
        // Make mutable reference to immutable to suppress compiler error for mutability mismatch.
        self.pat_arena.alloc(pat)
    }
}