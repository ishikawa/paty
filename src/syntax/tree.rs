use crate::syntax::{RangeEnd, Token, TokenKind};
use crate::ty::{FunctionSignature, NamedTy, StructTy, Type, TypeContext, TypedField};
use std::cell::Cell;
use std::fmt;
use std::iter::Peekable;
use std::slice;
use thiserror::Error;
use typed_arena::Arena;

#[derive(Error, Debug)]
pub enum ParseError<'t> {
    // Token iterator was not consumed, so you can safely retry to parse another node.
    #[error("parser did't met an expected token")]
    NotParsed,
    #[error("expected {expected}, but was {actual}")]
    UnexpectedToken { expected: String, actual: &'t Token },
    #[error("expected pattern, but was expr: {src}")]
    UnrecognizedPattern { src: String },
    #[error("premature end of file")]
    PrematureEnd,
}

pub trait Node {
    fn data(&self) -> &NodeData;
    fn data_mut(&mut self) -> &mut NodeData;
}

#[derive(Debug, Default)]
pub struct NodeData {
    // comments followed by this node.
    comments: Vec<String>,
}

impl NodeData {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
    }

    pub fn append_comments_from_token(&mut self, token: &Token) {
        for comment in token.comments() {
            self.comments.push(comment.to_string());
        }
    }

    pub fn append_comments_from_node(&mut self, node: &dyn Node) {
        for comment in node.data().comments() {
            self.comments.push(comment.to_string());
        }
    }
}

#[derive(Debug)]
pub enum TopLevel<'nd, 'tcx> {
    Declaration(Declaration<'nd, 'tcx>),
    Stmt(Stmt<'nd, 'tcx>),
}

#[derive(Debug)]
pub struct Declaration<'nd, 'tcx> {
    kind: DeclarationKind<'nd, 'tcx>,
    data: NodeData,
}

impl<'nd, 'tcx> Declaration<'nd, 'tcx> {
    pub fn new(kind: DeclarationKind<'nd, 'tcx>) -> Self {
        Self {
            kind,
            data: NodeData::new(),
        }
    }

    pub fn kind(&self) -> &DeclarationKind<'nd, 'tcx> {
        &self.kind
    }
}

impl<'nd, 'tcx> Node for Declaration<'nd, 'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

#[derive(Debug)]
pub enum DeclarationKind<'nd, 'tcx> {
    Function(Function<'nd, 'tcx>),
    Struct(StructDeclaration<'tcx>),
}

#[derive(Debug)]
pub struct Stmt<'nd, 'tcx> {
    kind: StmtKind<'nd, 'tcx>,
    data: NodeData,
}

impl<'nd, 'tcx> Stmt<'nd, 'tcx> {
    pub fn new(kind: StmtKind<'nd, 'tcx>) -> Self {
        Self {
            kind,
            data: NodeData::new(),
        }
    }

    pub fn kind(&self) -> &StmtKind<'nd, 'tcx> {
        &self.kind
    }
}

impl<'nd, 'tcx> Node for Stmt<'nd, 'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

#[derive(Debug)]
pub enum StmtKind<'nd, 'tcx> {
    Let {
        pattern: &'nd Pattern<'nd, 'tcx>,
        rhs: &'nd Expr<'nd, 'tcx>,
    },
    Expr(&'nd Expr<'nd, 'tcx>),
}

#[derive(Debug)]
pub struct Expr<'nd, 'tcx> {
    kind: ExprKind<'nd, 'tcx>,
    // The type of expression is determined in later phase.
    ty: Cell<Option<&'tcx Type<'tcx>>>,
    data: NodeData,
}

impl<'nd, 'tcx> Expr<'nd, 'tcx> {
    pub fn new(kind: ExprKind<'nd, 'tcx>) -> Self {
        Self {
            kind,
            ty: Cell::new(None),
            data: NodeData::new(),
        }
    }

    pub fn kind(&self) -> &ExprKind<'nd, 'tcx> {
        &self.kind
    }

    pub fn ty(&self) -> Option<&'tcx Type<'tcx>> {
        self.ty.get()
    }

    pub fn expect_ty(&self) -> &'tcx Type<'tcx> {
        self.ty().unwrap_or_else(|| {
            panic!(
                "Semantic analyzer couldn't assign type for expression {:?}",
                self
            );
        })
    }

    pub fn assign_ty(&self, ty: &'tcx Type<'tcx>) {
        self.ty.set(Some(ty))
    }
}

impl<'nd, 'tcx> Node for Expr<'nd, 'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

impl fmt::Display for Expr<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

#[derive(Debug)]
pub enum ExprKind<'nd, 'tcx> {
    Integer(i64),
    Boolean(bool),
    String(String),
    Var(String),
    Tuple(Vec<&'nd Expr<'nd, 'tcx>>),
    Struct(StructValue<'nd, 'tcx>),
    AnonStruct(AnonStructValue<'nd, 'tcx>),

    // unary operators
    Minus(&'nd Expr<'nd, 'tcx>),

    // binary operators
    Add(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Sub(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Mul(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Div(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Eq(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Ne(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Le(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Ge(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Lt(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Gt(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    And(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),
    Or(&'nd Expr<'nd, 'tcx>, &'nd Expr<'nd, 'tcx>),

    // tuple.0, tuple.1, ...
    IndexAccess(&'nd Expr<'nd, 'tcx>, usize),
    // struct.a, struct.b, ...
    FieldAccess(&'nd Expr<'nd, 'tcx>, String),

    Call(CallExpr<'nd, 'tcx>),
    Case {
        head: &'nd Expr<'nd, 'tcx>,
        arms: Vec<CaseArm<'nd, 'tcx>>,
        else_body: Option<&'nd Expr<'nd, 'tcx>>,
    },

    // Built-in functions
    Puts(Vec<&'nd Expr<'nd, 'tcx>>),
}

impl fmt::Display for ExprKind<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprKind::Integer(n) => n.fmt(f),
            ExprKind::Boolean(b) => b.fmt(f),
            ExprKind::String(s) => s.escape_default().fmt(f),
            ExprKind::Var(name) => name.fmt(f),
            ExprKind::Tuple(fs) => {
                write!(f, "(")?;
                let mut it = fs.iter().peekable();
                while let Some(a) = it.next() {
                    write!(f, "{}", a)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            ExprKind::AnonStruct(value) => value.fmt(f),
            ExprKind::Struct(value) => value.fmt(f),
            ExprKind::Minus(operand) => write!(f, "-{}", operand),
            ExprKind::Add(a, b) => write!(f, "{} + {}", a, b),
            ExprKind::Sub(a, b) => write!(f, "{} - {}", a, b),
            ExprKind::Mul(a, b) => write!(f, "{} * {}", a, b),
            ExprKind::Div(a, b) => write!(f, "{} / {}", a, b),
            ExprKind::Eq(a, b) => write!(f, "{} == {}", a, b),
            ExprKind::Ne(a, b) => write!(f, "{} != {}", a, b),
            ExprKind::Le(a, b) => write!(f, "{} <= {}", a, b),
            ExprKind::Ge(a, b) => write!(f, "{} >= {}", a, b),
            ExprKind::Lt(a, b) => write!(f, "{} < {}", a, b),
            ExprKind::Gt(a, b) => write!(f, "{} > {}", a, b),
            ExprKind::And(a, b) => write!(f, "{} && {}", a, b),
            ExprKind::Or(a, b) => write!(f, "{} || {}", a, b),
            ExprKind::IndexAccess(operand, i) => write!(f, "{}.{}", operand, i),
            ExprKind::FieldAccess(operand, name) => write!(f, "{}.{}", operand, name),
            ExprKind::Call(call_expr) => call_expr.fmt(f),
            ExprKind::Case {
                head,
                arms,
                else_body,
            } => {
                writeln!(f, "case {}", head)?;
                for arm in arms {
                    writeln!(f, "when {:?}", arm.pattern())?;
                    writeln!(f, "  {}", arm.body())?;
                }
                if let Some(else_body) = else_body {
                    writeln!(f, "else")?;
                    writeln!(f, "  {}", else_body)?;
                }
                write!(f, "end")
            }
            ExprKind::Puts(args) => {
                write!(f, "puts(")?;
                let mut it = args.iter().peekable();
                while let Some(a) = it.next() {
                    write!(f, "{}", a)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug)]
pub struct CallExpr<'nd, 'tcx> {
    name: String,
    args: Vec<&'nd Expr<'nd, 'tcx>>,
    /// Resolved overloaded function.
    function: Cell<Option<&'nd Function<'nd, 'tcx>>>,
}

impl<'nd, 'tcx> CallExpr<'nd, 'tcx> {
    pub fn new(name: String, args: Vec<&'nd Expr<'nd, 'tcx>>) -> Self {
        Self {
            name,
            args,
            function: Cell::new(None),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn arguments(&self) -> &[&'nd Expr<'nd, 'tcx>] {
        &self.args
    }

    pub fn function(&self) -> Option<&'nd Function<'nd, 'tcx>> {
        self.function.get()
    }

    pub fn assign_function(&self, fun: &'nd Function<'nd, 'tcx>) {
        self.function.set(Some(fun));
    }
}

impl fmt::Display for CallExpr<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        write!(f, "(")?;
        let mut it = self.args.iter().peekable();
        while let Some(a) = it.next() {
            write!(f, "{}", a)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

#[derive(Debug)]
pub struct Function<'nd, 'tcx> {
    name: String,
    params: Vec<Parameter<'nd, 'tcx>>,
    body: Vec<Stmt<'nd, 'tcx>>,
}

impl<'nd, 'tcx> Function<'nd, 'tcx> {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn params(&self) -> &[Parameter<'nd, 'tcx>] {
        &self.params
    }

    pub fn body(&self) -> &[Stmt<'nd, 'tcx>] {
        &self.body
    }

    pub fn retty(&self) -> Option<&'tcx Type<'tcx>> {
        if let Some(stmt) = self.body.last() {
            if let StmtKind::Expr(e) = stmt.kind() {
                return e.ty();
            }
        }
        None
    }

    pub fn signature(&self) -> FunctionSignature<'tcx> {
        let params = self.params().iter().map(|p| p.ty()).collect();
        FunctionSignature::new(self.name.clone(), params)
    }
}

/// Formal parameter for a function
#[derive(Debug)]
pub struct Parameter<'nd, 'tcx> {
    pattern: &'nd Pattern<'nd, 'tcx>,
    ty: &'tcx Type<'tcx>,
    data: NodeData,
}

impl<'nd, 'tcx> Parameter<'nd, 'tcx> {
    pub fn new(pattern: &'nd Pattern<'nd, 'tcx>, ty: &'tcx Type<'tcx>) -> Self {
        Self {
            pattern,
            ty,
            data: NodeData::new(),
        }
    }

    pub fn pattern(&self) -> &'nd Pattern<'nd, 'tcx> {
        self.pattern
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }
}

impl<'nd, 'tcx> Node for Parameter<'nd, 'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

#[derive(Debug)]
pub struct StructDeclaration<'tcx> {
    name: String,
    fields: Vec<StructFieldDef<'tcx>>,
    ty: &'tcx Type<'tcx>,
}

impl<'tcx> StructDeclaration<'tcx> {
    pub fn new(name: &str, fields: Vec<StructFieldDef<'tcx>>, ty: &'tcx Type<'tcx>) -> Self {
        Self {
            name: name.to_string(),
            fields,
            ty,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fields(&self) -> &[StructFieldDef<'tcx>] {
        &self.fields
    }

    pub fn is_empty(&self) -> bool {
        self.fields.is_empty()
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }
}

#[derive(Debug)]
pub struct StructFieldDef<'tcx> {
    name: String,
    ty: &'tcx Type<'tcx>,
    data: NodeData,
}

impl<'tcx> StructFieldDef<'tcx> {
    pub fn new(name: &str, ty: &'tcx Type<'tcx>) -> Self {
        Self {
            name: name.to_string(),
            ty,
            data: NodeData::new(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }
}

impl<'tcx> Node for StructFieldDef<'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

#[derive(Debug)]
pub struct StructValueBody<'nd, 'tcx> {
    fields: Vec<ValueFieldOrSpread<'nd, 'tcx>>,
}

impl<'nd, 'tcx> StructValueBody<'nd, 'tcx> {
    pub fn new(fields: Vec<ValueFieldOrSpread<'nd, 'tcx>>) -> Self {
        Self { fields }
    }

    pub fn fields(&self) -> &[ValueFieldOrSpread<'nd, 'tcx>] {
        &self.fields
    }
}

impl fmt::Display for StructValueBody<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut it = self.fields().iter().peekable();
        let empty = it.peek().is_none();

        write!(f, "{{")?;
        if !empty {
            write!(f, " ")?;
        }
        while let Some(field) = it.next() {
            field.fmt(f)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        if !empty {
            write!(f, " ")?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug)]
pub struct AnonStructValue<'nd, 'tcx> {
    body: StructValueBody<'nd, 'tcx>,
}

impl<'nd, 'tcx> AnonStructValue<'nd, 'tcx> {
    pub fn new(fields: Vec<ValueFieldOrSpread<'nd, 'tcx>>) -> Self {
        let body = StructValueBody::new(fields);
        Self { body }
    }

    pub fn fields(&self) -> &[ValueFieldOrSpread<'nd, 'tcx>] {
        self.body.fields()
    }
}

impl fmt::Display for AnonStructValue<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body)
    }
}

#[derive(Debug)]
pub struct StructValue<'nd, 'tcx> {
    name: String,
    body: StructValueBody<'nd, 'tcx>,
}

impl<'nd, 'tcx> StructValue<'nd, 'tcx> {
    pub fn new(name: String, fields: Vec<ValueFieldOrSpread<'nd, 'tcx>>) -> Self {
        let body = StructValueBody::new(fields);
        Self { name, body }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fields(&self) -> &[ValueFieldOrSpread<'nd, 'tcx>] {
        self.body.fields()
    }
}

impl fmt::Display for StructValue<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "struct {} ", self.name())?;
        write!(f, "{}", self.body)
    }
}

#[derive(Debug)]
pub struct SpreadExpr<'nd, 'tcx> {
    operand: Option<&'nd Expr<'nd, 'tcx>>,
}

impl<'nd, 'tcx> SpreadExpr<'nd, 'tcx> {
    pub fn new(operand: Option<&'nd Expr<'nd, 'tcx>>) -> Self {
        Self { operand }
    }

    pub fn operand(&self) -> Option<&'nd Expr<'nd, 'tcx>> {
        self.operand
    }
}

impl fmt::Display for SpreadExpr<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "...")?;
        if let Some(expr) = self.operand {
            write!(f, "{}", expr)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct CaseArm<'nd, 'tcx> {
    pattern: &'nd Pattern<'nd, 'tcx>,
    body: &'nd Expr<'nd, 'tcx>,
    data: NodeData,
}

impl<'nd, 'tcx> CaseArm<'nd, 'tcx> {
    pub fn new(pattern: &'nd Pattern<'nd, 'tcx>, body: &'nd Expr<'nd, 'tcx>) -> Self {
        Self {
            pattern,
            body,
            data: NodeData::new(),
        }
    }

    pub fn pattern(&self) -> &'nd Pattern<'nd, 'tcx> {
        self.pattern
    }

    pub fn body(&self) -> &'nd Expr<'nd, 'tcx> {
        self.body
    }
}

impl<'nd, 'tcx> Node for CaseArm<'nd, 'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

#[derive(Debug)]
pub struct Pattern<'nd, 'tcx> {
    kind: PatternKind<'nd, 'tcx>,
    // The type of expression is determined in later phase.
    ty: Cell<Option<&'tcx Type<'tcx>>>,
    data: NodeData,
}

impl<'nd, 'tcx> Pattern<'nd, 'tcx> {
    pub fn new(kind: PatternKind<'nd, 'tcx>) -> Self {
        Self {
            kind,
            ty: Cell::new(None),
            data: NodeData::new(),
        }
    }

    pub fn kind(&self) -> &PatternKind<'nd, 'tcx> {
        &self.kind
    }

    pub fn ty(&self) -> Option<&'tcx Type<'tcx>> {
        self.ty.get()
    }

    pub fn expect_ty(&self) -> &'tcx Type<'tcx> {
        self.ty().unwrap_or_else(|| {
            panic!(
                "Semantic analyzer couldn't assign type for pattern {}",
                self.kind
            );
        })
    }

    pub fn assign_ty(&self, ty: &'tcx Type<'tcx>) {
        self.ty.set(Some(ty))
    }
}

impl<'nd, 'tcx> Node for Pattern<'nd, 'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

#[derive(Debug)]
pub enum PatternKind<'nd, 'tcx> {
    Integer(i64),
    Boolean(bool),
    String(String),
    Range { lo: i64, hi: i64, end: RangeEnd },
    Tuple(Vec<&'nd Pattern<'nd, 'tcx>>),
    AnonStruct(AnonStructPattern<'nd, 'tcx>),
    Struct(StructPattern<'nd, 'tcx>),
    Var(String),
    Wildcard,
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
            PatternKind::Tuple(patterns) => {
                let mut it = patterns.iter().peekable();
                write!(f, "(")?;
                while let Some(sub_pat) = it.next() {
                    write!(f, "{}", sub_pat.kind())?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            PatternKind::AnonStruct(struct_pat) => struct_pat.fmt(f),
            PatternKind::Struct(struct_pat) => struct_pat.fmt(f),
            PatternKind::Var(name) => write!(f, "{}", name),
            PatternKind::Wildcard => write!(f, "_"),
        }
    }
}

#[derive(Debug)]
pub struct StructPatternBody<'nd, 'tcx> {
    fields: Vec<PatternFieldOrSpread<'nd, 'tcx>>,
}

impl<'nd, 'tcx> StructPatternBody<'nd, 'tcx> {
    pub fn new(fields: Vec<PatternFieldOrSpread<'nd, 'tcx>>) -> Self {
        Self { fields }
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &PatternFieldOrSpread<'nd, 'tcx>> {
        self.fields.iter()
    }

    pub fn get_field(&self, name: &str) -> Option<&PatternField<'nd, 'tcx>> {
        for f in &self.fields {
            if let PatternFieldOrSpread::PatternField(f) = f {
                if f.name() == name {
                    return Some(f);
                }
            }
        }
        None
    }
}

impl fmt::Display for StructPatternBody<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut it = self.fields().peekable();
        let empty = it.peek().is_none();
        write!(f, "{{")?;
        if !empty {
            write!(f, " ")?;
        }
        while let Some(field) = it.next() {
            field.fmt(f)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        if !empty {
            write!(f, " ")?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug)]
pub enum ValueFieldOrSpread<'nd, 'tcx> {
    ValueField(ValueField<'nd, 'tcx>),
    Spread(SpreadExpr<'nd, 'tcx>),
}

impl fmt::Display for ValueFieldOrSpread<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValueFieldOrSpread::ValueField(field) => field.fmt(f),
            ValueFieldOrSpread::Spread(spread) => spread.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct ValueField<'nd, 'tcx> {
    name: String,
    value: &'nd Expr<'nd, 'tcx>,
    data: NodeData,
}

impl<'nd, 'tcx> ValueField<'nd, 'tcx> {
    pub fn new(name: &str, value: &'nd Expr<'nd, 'tcx>) -> Self {
        Self {
            name: name.to_string(),
            value,
            data: NodeData::new(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn value(&self) -> &'nd Expr<'nd, 'tcx> {
        self.value
    }
}

impl fmt::Display for ValueField<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)?;
        write!(f, ": ")?;
        write!(f, "{}", self.value)
    }
}

impl<'nd, 'tcx> Node for ValueField<'nd, 'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

#[derive(Debug)]
pub struct AnonStructPattern<'nd, 'tcx> {
    body: StructPatternBody<'nd, 'tcx>,
}

impl<'nd, 'tcx> AnonStructPattern<'nd, 'tcx> {
    pub fn new(fields: Vec<PatternFieldOrSpread<'nd, 'tcx>>) -> Self {
        let body = StructPatternBody::new(fields);
        Self { body }
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &PatternFieldOrSpread<'nd, 'tcx>> {
        self.body.fields()
    }

    pub fn get_field(&self, name: &str) -> Option<&PatternField<'nd, 'tcx>> {
        self.body.get_field(name)
    }
}

impl fmt::Display for AnonStructPattern<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body)
    }
}

#[derive(Debug)]
pub struct StructPattern<'nd, 'tcx> {
    name: String,
    body: StructPatternBody<'nd, 'tcx>,
}

impl<'nd, 'tcx> StructPattern<'nd, 'tcx> {
    pub fn new(name: String, fields: Vec<PatternFieldOrSpread<'nd, 'tcx>>) -> Self {
        let body = StructPatternBody::new(fields);
        Self { name, body }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &PatternFieldOrSpread<'nd, 'tcx>> {
        self.body.fields()
    }

    pub fn get_field(&self, name: &str) -> Option<&PatternField<'nd, 'tcx>> {
        self.body.get_field(name)
    }
}

impl fmt::Display for StructPattern<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ", self.name())?;
        write!(f, "{}", self.body)
    }
}

#[derive(Debug)]
pub struct SpreadPattern {
    name: Option<String>,
}

impl SpreadPattern {
    pub fn new(name: Option<String>) -> Self {
        Self { name }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
}

impl fmt::Display for SpreadPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "...")?;
        if let Some(name) = &self.name {
            name.fmt(f)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum PatternFieldOrSpread<'nd, 'tcx> {
    PatternField(PatternField<'nd, 'tcx>),
    Spread(SpreadPattern),
}

impl fmt::Display for PatternFieldOrSpread<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternFieldOrSpread::PatternField(field) => field.fmt(f),
            PatternFieldOrSpread::Spread(spread) => spread.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct PatternField<'nd, 'tcx> {
    name: String,
    pattern: &'nd Pattern<'nd, 'tcx>,
    data: NodeData,
}

impl<'nd, 'tcx> PatternField<'nd, 'tcx> {
    pub fn new(name: String, pattern: &'nd Pattern<'nd, 'tcx>) -> Self {
        Self {
            name,
            pattern,
            data: NodeData::new(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn pattern(&self) -> &'nd Pattern<'nd, 'tcx> {
        self.pattern
    }
}

impl fmt::Display for PatternField<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.name())?;
        write!(f, "{}", self.pattern().kind())
    }
}

impl<'nd, 'tcx> Node for PatternField<'nd, 'tcx> {
    fn data(&self) -> &NodeData {
        &self.data
    }

    fn data_mut(&mut self) -> &mut NodeData {
        &mut self.data
    }
}

pub struct Parser<'nd, 'tcx> {
    pub tcx: TypeContext<'tcx>,
    pub expr_arena: &'nd Arena<Expr<'nd, 'tcx>>,
    pub pat_arena: &'nd Arena<Pattern<'nd, 'tcx>>,
}

pub type ParseResult<'t, 'nd, 'tcx> = Result<&'nd Expr<'nd, 'tcx>, ParseError<'t>>;

type TokenIterator<'t> = Peekable<slice::Iter<'t, Token>>;

#[allow(dead_code)]
impl<'t, 'nd, 'tcx> Parser<'nd, 'tcx> {
    pub fn new(
        tcx: TypeContext<'tcx>,
        expr_arena: &'nd Arena<Expr<'nd, 'tcx>>,
        pat_arena: &'nd Arena<Pattern<'nd, 'tcx>>,
    ) -> Self {
        Self {
            tcx,
            expr_arena,
            pat_arena,
        }
    }

    pub fn parse(&self, tokens: &'t [Token]) -> Result<Vec<TopLevel<'nd, 'tcx>>, ParseError<'t>> {
        let mut it = tokens.iter().peekable();
        let mut body = vec![];

        while it.peek().is_some() {
            if let Some(top_level) = self.lookahead(self.top_level(&mut it))? {
                body.push(top_level);
            }
        }

        if let Some(token) = it.peek() {
            Err(ParseError::UnexpectedToken {
                expected: "(EOF)".to_string(),
                actual: token,
            })
        } else {
            Ok(body)
        }
    }

    // --- Parser

    fn top_level(&self, it: &mut TokenIterator<'t>) -> Result<TopLevel<'nd, 'tcx>, ParseError<'t>> {
        if let Some(decl) = self.lookahead(self.decl(it))? {
            Ok(TopLevel::Declaration(decl))
        } else if let Some(stmt) = self.lookahead(self.stmt(it))? {
            Ok(TopLevel::Stmt(stmt))
        } else {
            Err(ParseError::NotParsed)
        }
    }

    fn decl(&self, it: &mut TokenIterator<'t>) -> Result<Declaration<'nd, 'tcx>, ParseError<'t>> {
        if let Some(r#fn) = self.lookahead(self.function_decl(it))? {
            Ok(r#fn)
        } else if let Some(r#struct) = self.lookahead(self.struct_decl(it))? {
            Ok(r#struct)
        } else {
            Err(ParseError::NotParsed)
        }
    }

    fn stmts(&self, it: &mut TokenIterator<'t>) -> Result<Vec<Stmt<'nd, 'tcx>>, ParseError<'t>> {
        let mut body = vec![];

        while let Some(stmt) = self.lookahead(self.stmt(it))? {
            body.push(stmt);
        }

        if body.is_empty() {
            Err(ParseError::NotParsed)
        } else {
            Ok(body)
        }
    }

    fn stmt(&self, it: &mut TokenIterator<'t>) -> Result<Stmt<'nd, 'tcx>, ParseError<'t>> {
        if let Some(expr) = self.lookahead(self.expr(it))? {
            // To make this LL(1) parser able to parse `assignment` grammar which is LL(2):
            //
            //     assignment -> pattern ASSIGN expr | expr
            //
            // First, we try to parse the grammar that is LL(1):
            //
            //     assignment -> expr ASSIGN expr | expr
            //
            // And then, construct an assignment node if the left hand of an assignment is
            // a pattern.
            let stmt = if self.match_token(it, TokenKind::Operator('=')) {
                // convert Expr to Pattern
                let pattern = self.expr_to_pattern(expr)?;
                it.next();

                let rhs = self.expr(it)?;
                let mut r#let = Stmt::new(StmtKind::Let { pattern, rhs });

                r#let.data_mut().append_comments_from_node(expr);
                r#let
            } else {
                Stmt::new(StmtKind::Expr(expr))
            };
            Ok(stmt)
        } else {
            Err(ParseError::NotParsed)
        }
    }

    fn function_decl(
        &self,
        it: &mut TokenIterator<'t>,
    ) -> Result<Declaration<'nd, 'tcx>, ParseError<'t>> {
        let def_token = self.try_token(it, TokenKind::Def)?;

        let name_token = self.peek_token(it)?;
        let name = if let TokenKind::Identifier(name) = name_token.kind() {
            it.next();
            name.clone()
        } else {
            return Err(ParseError::UnexpectedToken {
                expected: "function name".to_string(),
                actual: name_token,
            });
        };

        let params = self.parse_elements(it, ('(', ')'), Self::function_parameter)?;

        let body = self.stmts(it)?;

        self.expect_token(it, TokenKind::End)?;

        let r#fn = Function { name, params, body };
        let mut decl = Declaration::new(DeclarationKind::Function(r#fn));

        decl.data_mut().append_comments_from_token(def_token);

        Ok(decl)
    }

    fn function_parameter(
        &self,
        it: &mut TokenIterator<'t>,
    ) -> Result<Parameter<'nd, 'tcx>, ParseError<'t>> {
        let pat = self.pattern(it)?;

        let ty = if self.match_token(it, TokenKind::Operator(':')) {
            it.next();

            self.type_specifier(it)?
        } else {
            // Int64 for omitted type
            self.tcx.int64()
        };

        let mut param = Parameter::new(pat, ty);
        param.data_mut().append_comments_from_node(pat);

        Ok(param)
    }

    fn struct_decl(
        &self,
        it: &mut TokenIterator<'t>,
    ) -> Result<Declaration<'nd, 'tcx>, ParseError<'t>> {
        let struct_token = self.try_token(it, TokenKind::Struct)?;

        let name_token = self.peek_token(it)?;
        let name = if let TokenKind::Identifier(name) = name_token.kind() {
            it.next();
            name.clone()
        } else {
            return Err(ParseError::UnexpectedToken {
                expected: "struct name".to_string(),
                actual: name_token,
            });
        };

        let fields = self.parse_elements(it, ('{', '}'), Self::struct_field_definition)?;

        // Build struct type
        let fs: Vec<TypedField<'_>> = fields
            .iter()
            .map(|f| TypedField::new(f.name().to_string(), f.ty()))
            .collect();
        let struct_ty = StructTy::new(name.to_string(), fs);
        let ty = self.tcx.type_arena.alloc(Type::Struct(struct_ty));

        let r#struct = StructDeclaration { name, fields, ty };
        let mut decl = Declaration::new(DeclarationKind::Struct(r#struct));

        decl.data_mut().append_comments_from_token(struct_token);

        Ok(decl)
    }

    fn struct_field_definition(
        &self,
        it: &mut TokenIterator<'t>,
    ) -> Result<StructFieldDef<'tcx>, ParseError<'t>> {
        let (name_token, name) = if let Some(t) = it.peek() {
            if let TokenKind::Identifier(name) = t.kind() {
                let t = it.next().unwrap();
                (t, name.to_string())
            } else {
                return Err(ParseError::NotParsed);
            }
        } else {
            return Err(ParseError::NotParsed);
        };

        self.expect_token(it, TokenKind::Operator(':'))?;

        let ty = self.type_specifier(it)?;

        let mut field = StructFieldDef::new(&name, ty);
        field.data_mut().append_comments_from_token(name_token);

        Ok(field)
    }

    fn value_field(
        &self,
        it: &mut TokenIterator<'t>,
    ) -> Result<ValueFieldOrSpread<'nd, 'tcx>, ParseError<'t>> {
        let start_token = if let Some(tok) = it.peek() {
            tok
        } else {
            return Err(ParseError::NotParsed);
        };

        match start_token.kind() {
            TokenKind::Spread => {
                it.next();

                // spread operator
                let operand = self.lookahead(self.expr(it))?;
                let spread = SpreadExpr::new(operand);
                Ok(ValueFieldOrSpread::Spread(spread))
            }
            TokenKind::Identifier(name) => {
                let name = name.to_string();
                let t = it.next().unwrap();

                // If a field value is omitted, it will be interpreted as an omitted variable
                // binding with the same name of the field.
                let value = if self.match_token(it, TokenKind::Operator(':')) {
                    it.next();
                    self.expr(it)?
                } else {
                    let kind = ExprKind::Var(name.to_string());
                    self.expr_arena.alloc(Expr::new(kind))
                };

                let mut field = ValueField::new(&name, value);
                field.data_mut().append_comments_from_token(t);

                Ok(ValueFieldOrSpread::ValueField(field))
            }
            _ => Err(ParseError::NotParsed),
        }
    }

    fn pattern_field(
        &self,
        it: &mut TokenIterator<'t>,
    ) -> Result<PatternFieldOrSpread<'nd, 'tcx>, ParseError<'t>> {
        let start_token = if let Some(tok) = it.peek() {
            tok
        } else {
            return Err(ParseError::NotParsed);
        };

        match start_token.kind() {
            TokenKind::Spread => {
                it.next();

                // spread pattern
                let name = if let TokenKind::Identifier(name) = self.peek_token(it)?.kind() {
                    it.next();
                    Some(name.to_string())
                } else {
                    None
                };

                let spread = SpreadPattern::new(name);
                Ok(PatternFieldOrSpread::Spread(spread))
            }
            TokenKind::Identifier(name) => {
                let name = name.to_string();
                let t = it.next().unwrap();

                // field
                // Variable pattern in field value can be omitted.
                let value_pat = if self.match_token(it, TokenKind::Operator(':')) {
                    it.next();
                    self.pattern(it)?
                } else {
                    let kind = PatternKind::Var(name.to_string());
                    self.pat_arena.alloc(Pattern::new(kind))
                };

                let mut field = PatternField::new(name, value_pat);
                field.data_mut().append_comments_from_token(t);

                Ok(PatternFieldOrSpread::PatternField(field))
            }
            _ => Err(ParseError::NotParsed),
        }
    }

    fn type_specifier(
        &self,
        it: &mut TokenIterator<'t>,
    ) -> Result<&'tcx Type<'tcx>, ParseError<'t>> {
        let token = self.peek_token(it)?;
        let ty = match token.kind() {
            TokenKind::TypeInt64 => {
                it.next();
                self.tcx.int64()
            }
            TokenKind::TypeBoolean => {
                it.next();
                self.tcx.boolean()
            }
            TokenKind::TypeString => {
                it.next();
                self.tcx.string()
            }
            TokenKind::Operator('(') => {
                it.next();

                // Try to parse tuple type.
                let mut value_types = vec![];

                while !self.match_token(it, TokenKind::Operator(')')) {
                    let ty = self.type_specifier(it)?;
                    value_types.push(ty);

                    // trailing comma allowed, if the number of values is `1`,
                    // it's mandatory.
                    if self.match_token(it, TokenKind::Operator(',')) {
                        it.next();
                    } else if value_types.len() == 1 {
                        return Err(ParseError::UnexpectedToken {
                            expected: "','".to_string(),
                            actual: self.peek_token(it)?,
                        });
                    }
                }
                // ')'
                it.next();

                self.tcx.tuple(&value_types)
            }
            TokenKind::Identifier(name) => {
                it.next();

                let ty = Type::Named(NamedTy::new(name));
                self.tcx.type_arena.alloc(ty)
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "type".to_string(),
                    actual: token,
                });
            }
        };
        Ok(ty)
    }

    // expressions

    fn expr(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        if let Some(expr) = self.lookahead(self.case(it))? {
            Ok(expr)
        } else {
            self.logical_op(it)
        }
    }

    // pattern
    fn pattern(
        &self,
        it: &mut TokenIterator<'t>,
    ) -> Result<&'nd Pattern<'nd, 'tcx>, ParseError<'t>> {
        let token = self.peek_token(it)?;
        let pat = match token.kind() {
            TokenKind::Integer(n) => {
                it.next();

                // range?
                let end = if self.match_token(it, TokenKind::RangeExcluded) {
                    it.next();
                    Some(RangeEnd::Excluded)
                } else if self.match_token(it, TokenKind::RangeIncluded) {
                    it.next();
                    Some(RangeEnd::Included)
                } else {
                    None
                };

                // build
                let i = n.parse().unwrap();

                let kind = if let Some(end) = end {
                    let hi_token = self.peek_token(it)?;
                    let hi = if let TokenKind::Integer(n) = hi_token.kind() {
                        it.next();
                        n.parse().unwrap()
                    } else {
                        return Err(ParseError::UnexpectedToken {
                            expected: "int".to_string(),
                            actual: hi_token,
                        });
                    };
                    PatternKind::Range { lo: i, hi, end }
                } else {
                    PatternKind::Integer(i)
                };

                self.alloc_pat(kind, token)
            }
            TokenKind::String(s) => {
                it.next();

                let kind = PatternKind::String(s.clone());
                self.alloc_pat(kind, token)
            }
            TokenKind::True => {
                it.next();

                let kind = PatternKind::Boolean(true);
                self.alloc_pat(kind, token)
            }
            TokenKind::False => {
                it.next();

                let kind = PatternKind::Boolean(false);
                self.alloc_pat(kind, token)
            }
            TokenKind::Operator('(') => {
                // tuple or grouping values.
                // - `()` -> empty tuple
                // - `(pat)` -> pattern
                // - `(pat,)` -> tuple (n = 1)
                // - `(pat1, pat2, ...)` tuple
                it.next(); // '('

                let mut comma_seen = false;
                let mut patterns = vec![];

                while !self.match_token(it, TokenKind::Operator(')')) {
                    if let Some(pat) = self.lookahead(self.pattern(it))? {
                        patterns.push(pat);
                    } else {
                        return Err(ParseError::UnexpectedToken {
                            expected: "pattern".to_string(),
                            actual: self.peek_token(it)?,
                        });
                    }

                    // tuple (n >= 1) must contain ','
                    if self.match_token(it, TokenKind::Operator(',')) {
                        it.next(); // ','
                        comma_seen = true;
                    }
                }
                it.next(); // ')'

                if comma_seen || patterns.is_empty() {
                    let kind = PatternKind::Tuple(patterns);
                    self.alloc_pat(kind, token)
                } else if patterns.len() == 1 {
                    patterns[0]
                } else {
                    unreachable!("invalid tuple or group");
                }
            }
            TokenKind::Identifier(name) => {
                it.next();
                if self.match_token(it, TokenKind::Operator('{')) {
                    let fields = self.parse_elements(it, ('{', '}'), Self::pattern_field)?;
                    let struct_value = StructPattern::new(name.to_string(), fields);
                    let kind = PatternKind::Struct(struct_value);
                    self.alloc_pat(kind, token)
                } else {
                    self.alloc_pat(self.variable_name_to_pattern(name), token)
                }
            }
            _ => {
                return Err(ParseError::NotParsed);
            }
        };

        Ok(pat)
    }

    fn expr_to_pattern(
        &self,
        expr: &'nd Expr<'nd, 'tcx>,
    ) -> Result<&'nd Pattern<'nd, 'tcx>, ParseError<'t>> {
        let kind = match expr.kind() {
            ExprKind::Var(name) => self.variable_name_to_pattern(name),
            ExprKind::Integer(n) => PatternKind::Integer(*n),
            ExprKind::Boolean(b) => PatternKind::Boolean(*b),
            ExprKind::String(s) => PatternKind::String(s.to_string()),
            ExprKind::Tuple(fs) => {
                let mut ps = vec![];

                for sub_expr in fs {
                    let sub_pat = self.expr_to_pattern(sub_expr)?;
                    ps.push(sub_pat);
                }

                PatternKind::Tuple(ps)
            }
            ExprKind::AnonStruct(struct_value) => {
                let fields = self.value_fields_to_pattern_fields(struct_value.fields())?;
                let struct_pat = AnonStructPattern::new(fields);

                PatternKind::AnonStruct(struct_pat)
            }
            ExprKind::Struct(struct_value) => {
                let fields = self.value_fields_to_pattern_fields(struct_value.fields())?;
                let struct_pat = StructPattern::new(struct_value.name().to_string(), fields);

                PatternKind::Struct(struct_pat)
            }
            ExprKind::Minus(_)
            | ExprKind::Add(_, _)
            | ExprKind::Sub(_, _)
            | ExprKind::Mul(_, _)
            | ExprKind::Div(_, _)
            | ExprKind::Eq(_, _)
            | ExprKind::Ne(_, _)
            | ExprKind::Le(_, _)
            | ExprKind::Ge(_, _)
            | ExprKind::Lt(_, _)
            | ExprKind::Gt(_, _)
            | ExprKind::And(_, _)
            | ExprKind::Or(_, _)
            | ExprKind::IndexAccess(_, _)
            | ExprKind::FieldAccess(_, _)
            | ExprKind::Call(_)
            | ExprKind::Case { .. }
            | ExprKind::Puts(_) => {
                return Err(ParseError::UnrecognizedPattern {
                    src: expr.to_string(),
                })
            }
        };

        Ok(self.pat_arena.alloc(Pattern::new(kind)))
    }

    fn value_fields_to_pattern_fields(
        &self,
        value_fields: &[ValueFieldOrSpread<'nd, 'tcx>],
    ) -> Result<Vec<PatternFieldOrSpread<'nd, 'tcx>>, ParseError<'t>> {
        let mut fields = vec![];

        for f in value_fields {
            match f {
                ValueFieldOrSpread::ValueField(field) => {
                    let field_pat = self.expr_to_pattern(field.value())?;
                    let field = PatternField::new(field.name().to_string(), field_pat);

                    fields.push(PatternFieldOrSpread::PatternField(field));
                }
                ValueFieldOrSpread::Spread(spread) => {
                    let spread_pat = if let Some(expr) = spread.operand {
                        if let ExprKind::Var(name) = expr.kind() {
                            SpreadPattern::new(Some(name.to_string()))
                        } else {
                            return Err(ParseError::UnrecognizedPattern {
                                src: expr.to_string(),
                            });
                        }
                    } else {
                        SpreadPattern::new(None)
                    };

                    fields.push(PatternFieldOrSpread::Spread(spread_pat));
                }
            }
        }

        Ok(fields)
    }

    fn variable_name_to_pattern(&self, name: &str) -> PatternKind<'nd, 'tcx> {
        if name == "_" {
            PatternKind::Wildcard
        } else {
            PatternKind::Var(name.to_string())
        }
    }

    fn case_arm(&self, it: &mut TokenIterator<'t>) -> Result<CaseArm<'nd, 'tcx>, ParseError<'t>> {
        let when_token = self.try_token(it, TokenKind::When)?;

        let pattern = self.pattern(it)?;
        let body = self.expr(it)?;

        let mut arm = CaseArm::new(pattern, body);
        arm.data_mut().append_comments_from_token(when_token);
        Ok(arm)
    }

    fn case(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        let case_token = self.try_token(it, TokenKind::Case)?;
        let head = self.expr(it)?;

        let mut arms = vec![];

        while let Some(arm) = self.lookahead(self.case_arm(it))? {
            arms.push(arm);
        }

        let else_body = if self.match_token(it, TokenKind::Else) {
            it.next();
            Some(self.expr(it)?)
        } else {
            None
        };

        self.expect_token(it, TokenKind::End)?;

        let kind = ExprKind::Case {
            head,
            arms,
            else_body,
        };

        Ok(self.alloc_expr(kind, case_token))
    }

    // logical operators
    fn logical_op(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        let lhs = self.eq_op(it)?;

        if let Some(token) = it.peek() {
            let op = match token.kind() {
                TokenKind::And => ExprKind::And,
                TokenKind::Or => ExprKind::Or,
                _ => {
                    return Ok(lhs);
                }
            };

            let token = it.next().unwrap();
            let rhs = self.eq_op(it)?;

            return Ok(self.alloc_expr(op(lhs, rhs), token));
        }

        Ok(lhs)
    }

    // equality operators
    fn eq_op(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        let lhs = self.comp_op(it)?;

        if let Some(token) = it.peek() {
            let op = match token.kind() {
                TokenKind::Eq => ExprKind::Eq,
                TokenKind::Ne => ExprKind::Ne,
                _ => {
                    return Ok(lhs);
                }
            };

            let token = it.next().unwrap();
            let rhs = self.comp_op(it)?;

            return Ok(self.alloc_expr(op(lhs, rhs), token));
        }

        Ok(lhs)
    }

    // comparison operators
    fn comp_op(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        let lhs = self.bin_op1(it)?;

        if let Some(token) = it.peek() {
            let op = match token.kind() {
                TokenKind::Operator('<') => ExprKind::Lt,
                TokenKind::Operator('>') => ExprKind::Gt,
                TokenKind::Le => ExprKind::Le,
                TokenKind::Ge => ExprKind::Ge,
                _ => {
                    return Ok(lhs);
                }
            };

            let token = it.next().unwrap();
            let rhs = self.bin_op2(it)?;

            return Ok(self.alloc_expr(op(lhs, rhs), token));
        }

        Ok(lhs)
    }

    fn bin_op1(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        let mut lhs = self.bin_op2(it)?;

        while let Some(token) = it.peek() {
            let op = match token.kind() {
                TokenKind::Operator('+') => ExprKind::Add,
                TokenKind::Operator('-') => ExprKind::Sub,
                _ => {
                    break;
                }
            };

            let token = it.next().unwrap();
            let rhs = self.bin_op2(it)?;
            lhs = self.alloc_expr(op(lhs, rhs), token);
        }

        Ok(lhs)
    }

    fn bin_op2(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        let mut lhs = self.unary(it)?;

        while let Some(token) = it.peek() {
            let op = match token.kind() {
                TokenKind::Operator('*') => ExprKind::Mul,
                TokenKind::Operator('/') => ExprKind::Div,
                _ => {
                    break;
                }
            };

            let token = it.next().unwrap();
            let rhs = self.unary(it)?;
            lhs = self.alloc_expr(op(lhs, rhs), token);
        }

        Ok(lhs)
    }

    fn unary(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        if self.match_token(it, TokenKind::Operator('-')) {
            let token = it.next().unwrap();
            let expr = self.access(it)?;

            Ok(self.alloc_expr(ExprKind::Minus(expr), token))
        } else {
            self.access(it)
        }
    }

    fn access(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        let mut lhs = self.atom(it)?;

        while self.match_token(it, TokenKind::Operator('.')) {
            let token = it.next().unwrap();

            let t = self.peek_token(it)?;
            match t.kind() {
                TokenKind::Integer(n) => {
                    // tuple element
                    it.next();
                    let index = n.parse().unwrap();
                    lhs = self.alloc_expr(ExprKind::IndexAccess(lhs, index), token);
                }
                TokenKind::Identifier(name) => {
                    // struct member / uniform function call
                    it.next();
                    lhs = if self.match_token(it, TokenKind::Operator('(')) {
                        let mut args = self.parse_elements(it, ('(', ')'), Self::expr)?;
                        args.insert(0, lhs);
                        self.alloc_expr(ExprKind::Call(CallExpr::new(name.clone(), args)), token)
                    } else {
                        self.alloc_expr(ExprKind::FieldAccess(lhs, name.to_string()), token)
                    };
                }
                TokenKind::Puts => {
                    // struct member / uniform function call
                    it.next();
                    lhs = if self.match_token(it, TokenKind::Operator('(')) {
                        let mut args = self.parse_elements(it, ('(', ')'), Self::expr)?;
                        args.insert(0, lhs);
                        self.alloc_expr(ExprKind::Puts(args), token)
                    } else {
                        self.alloc_expr(ExprKind::FieldAccess(lhs, "puts".to_string()), token)
                    };
                }
                _ => {
                    return Err(ParseError::UnexpectedToken {
                        expected: "index".to_string(),
                        actual: t,
                    });
                }
            }
        }

        Ok(lhs)
    }

    fn atom(&self, it: &mut TokenIterator<'t>) -> ParseResult<'t, 'nd, 'tcx> {
        let token = self.peek_token(it)?;
        let kind = match token.kind() {
            TokenKind::Integer(n) => {
                it.next();

                let i = n.parse().unwrap();
                ExprKind::Integer(i)
            }
            TokenKind::Identifier(name) => {
                it.next();

                // call/struct/var
                if self.match_token(it, TokenKind::Operator('(')) {
                    let args = self.parse_elements(it, ('(', ')'), Self::expr)?;
                    ExprKind::Call(CallExpr::new(name.clone(), args))
                } else if self.match_token(it, TokenKind::Operator('{')) {
                    let fields = self.parse_elements(it, ('{', '}'), Self::value_field)?;
                    let struct_value = StructValue::new(name.to_string(), fields);
                    ExprKind::Struct(struct_value)
                } else {
                    ExprKind::Var(name.clone())
                }
            }
            TokenKind::Puts => {
                it.next();

                let args = self.parse_elements(it, ('(', ')'), Self::expr)?;
                ExprKind::Puts(args)
            }
            TokenKind::String(s) => {
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
                // tuple or grouping values.
                // - `()` -> empty tuple
                // - `(expr)` -> expr
                // - `(expr,)` -> tuple (n = 1)
                // - `(expr1, expr2, ...)` tuple
                self.expect_token(it, TokenKind::Operator('('))?;

                let mut comma_seen = false;
                let mut exprs = vec![];

                while !self.match_token(it, TokenKind::Operator(')')) {
                    if let Some(pat) = self.lookahead(self.expr(it))? {
                        exprs.push(pat);
                    } else {
                        return Err(ParseError::UnexpectedToken {
                            expected: "expr".to_string(),
                            actual: self.peek_token(it)?,
                        });
                    }

                    // tuple (n >= 1) must contain ','
                    if self.match_token(it, TokenKind::Operator(',')) {
                        it.next(); // ','
                        comma_seen = true;
                    }
                }
                self.expect_token(it, TokenKind::Operator(')'))?;

                let expr = if comma_seen || exprs.is_empty() {
                    let kind = ExprKind::Tuple(exprs);
                    self.alloc_expr(kind, token)
                } else if exprs.len() == 1 {
                    exprs[0]
                } else {
                    unreachable!("invalid tuple or group");
                };

                return Ok(expr);
            }
            _ => {
                return Err(ParseError::NotParsed);
            }
        };

        Ok(self.alloc_expr(kind, token))
    }

    // --- Misc
    fn parse_elements<T>(
        &self,
        it: &mut TokenIterator<'t>,
        enclosing_char: (char, char),
        parser: fn(&Self, it: &mut TokenIterator<'t>) -> Result<T, ParseError<'t>>,
    ) -> Result<Vec<T>, ParseError<'t>> {
        let mut args = vec![];

        self.expect_token(it, TokenKind::Operator(enclosing_char.0))?;
        {
            while let Some(arg) = self.lookahead(parser(self, it))? {
                args.push(arg);

                // trailing comma can be omitted
                if self.match_token(it, TokenKind::Operator(',')) {
                    it.next();
                } else if !self.match_token(it, TokenKind::Operator(enclosing_char.1)) {
                    let actual = self.peek_token(it)?;
                    return Err(ParseError::UnexpectedToken {
                        expected: format!("'{}' or ','", enclosing_char.1),
                        actual,
                    });
                }
            }
        }
        self.expect_token(it, TokenKind::Operator(enclosing_char.1))?;
        Ok(args)
    }

    // look_

    fn match_token(&self, it: &mut TokenIterator<'t>, kind: TokenKind) -> bool {
        it.peek().filter(|token| *token.kind() == kind).is_some()
    }

    fn try_token(
        &self,
        it: &mut TokenIterator<'t>,
        kind: TokenKind,
    ) -> Result<&'t Token, ParseError<'t>> {
        if let Some(token) = it.peek() {
            if *token.kind() == kind {
                return Ok(it.next().unwrap());
            }
        }

        Err(ParseError::NotParsed)
    }

    fn peek_token(&self, it: &mut TokenIterator<'t>) -> Result<&'t Token, ParseError<'t>> {
        Ok(it.peek().ok_or(ParseError::PrematureEnd)?)
        //Ok(it.peek().unwrap())
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

    fn lookahead<T>(&self, r: Result<T, ParseError<'t>>) -> Result<Option<T>, ParseError<'t>> {
        match r {
            Ok(expr) => Ok(Some(expr)),
            Err(ParseError::NotParsed) => Ok(None),
            Err(err) => Err(err),
        }
    }

    fn alloc_expr(&self, kind: ExprKind<'nd, 'tcx>, token: &Token) -> &'nd Expr<'nd, 'tcx> {
        let mut expr = Expr::new(kind);
        expr.data_mut().append_comments_from_token(token);

        self.expr_arena.alloc(expr)
    }

    fn alloc_pat(&self, kind: PatternKind<'nd, 'tcx>, token: &Token) -> &'nd Pattern<'nd, 'tcx> {
        let mut pat = Pattern::new(kind);
        pat.data_mut().append_comments_from_token(token);

        self.pat_arena.alloc(pat)
    }
}
