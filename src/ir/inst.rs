use crate::ty::{FunctionSignature, Type, TypeContext};
use std::cell::Cell;
use std::fmt;

const DISPLAY_INDENT: &str = "  ";

#[derive(Debug, Default)]
pub struct Program<'a, 'tcx> {
    decl_types: Vec<&'tcx Type<'tcx>>,
    functions: Vec<Function<'a, 'tcx>>,
    pub entry_point: Option<Function<'a, 'tcx>>,
}

impl<'a, 'tcx> Program<'a, 'tcx> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn functions(&self) -> &[Function<'a, 'tcx>] {
        self.functions.as_slice()
    }

    pub fn functions_mut(&mut self) -> &mut [Function<'a, 'tcx>] {
        self.functions.as_mut_slice()
    }

    pub fn push_function(&mut self, fun: Function<'a, 'tcx>) {
        self.functions.push(fun);
    }

    pub fn add_decl_type(&mut self, ty: &'tcx Type<'tcx>) {
        if self.decl_types.contains(&ty) {
            return;
        }

        // To follow forward declaration rule, add field types first.
        match ty {
            Type::Tuple(fs) => {
                for fty in fs {
                    self.add_decl_type(fty);
                }
            }
            Type::Struct(struct_ty) => {
                for f in struct_ty.fields() {
                    self.add_decl_type(f.ty());
                }
            }
            Type::Union(member_types) => {
                for mty in member_types {
                    self.add_decl_type(mty);
                }
            }
            Type::Int64
            | Type::Boolean
            | Type::String
            | Type::NativeInt
            | Type::LiteralInt64(_)
            | Type::LiteralBoolean(_)
            | Type::LiteralString(_) => {
                // no declaration
                return;
            }
            Type::Named(named_ty) => {
                // no declaration
                self.add_decl_type(named_ty.expect_ty());
                return;
            }
            Type::Undetermined => unreachable!("untyped code"),
        };

        self.decl_types.push(ty);
    }

    pub fn decl_types(&self) -> impl Iterator<Item = &Type<'tcx>> {
        self.decl_types.iter().copied()
    }
}

impl fmt::Display for Program<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for fun in &self.functions {
            write!(f, "{}", fun)?;
        }
        if let Some(fun) = &self.entry_point {
            write!(f, "{}", fun)?;
        }
        Ok(())
    }
}

/// A function instruction.
///
/// The function signature of the main function must be:
///
/// ```ignore
/// main(void) -> int32
/// ```
#[derive(Debug)]
pub struct Function<'a, 'tcx> {
    name: String,
    signature: FunctionSignature<'tcx>,
    retty: &'tcx Type<'tcx>,
    pub params: Vec<Parameter<'a, 'tcx>>,
    pub body: Vec<&'a Stmt<'a, 'tcx>>,
}

impl<'a, 'tcx> Function<'a, 'tcx> {
    pub fn new(name: String, signature: FunctionSignature<'tcx>, retty: &'tcx Type<'tcx>) -> Self {
        Self {
            name,
            signature,
            retty,
            params: vec![],
            body: vec![],
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn retty(&self) -> &'tcx Type<'tcx> {
        self.retty
    }

    pub fn signature(&self) -> &FunctionSignature<'tcx> {
        &self.signature
    }
}

impl fmt::Display for Function<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        write!(f, "(")?;
        for (i, param) in self.params.iter().enumerate() {
            write!(f, "{}", param)?;
            if i < (self.params.len() - 1) {
                write!(f, ", ")?;
            }
        }
        writeln!(f, "):")?;
        for stmt in &self.body {
            let lines = stmt.to_string();
            let lines = lines.split('\n');
            for line in lines {
                write!(f, "{}", DISPLAY_INDENT)?;
                writeln!(f, "{}", line)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Parameter<'a, 'tcx> {
    TmpVar(&'a TmpVar<'a, 'tcx>),
    Var(Var<'tcx>),
}

impl<'a, 'tcx> Parameter<'a, 'tcx> {
    pub fn ty(&self) -> &'tcx Type<'tcx> {
        match self {
            Self::TmpVar(t) => t.ty,
            Self::Var(var) => var.ty,
        }
    }
}

impl fmt::Display for Parameter<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TmpVar(t) => t.fmt(f),
            Self::Var(name) => name.fmt(f),
        }?;
        write!(f, ": ")?;
        match self {
            Self::TmpVar(t) => t.ty.fmt(f),
            Self::Var(var) => var.ty.fmt(f),
        }
    }
}

// TODO: Unify temporary variables and regular variables so that
// unnecessary assignment elimination can work in either case.
#[derive(Debug, Clone)]
pub struct Var<'tcx> {
    name: String,
    ty: &'tcx Type<'tcx>,
}

impl<'tcx> Var<'tcx> {
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

impl fmt::Display for Var<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)
    }
}

#[derive(Debug)]
pub struct TmpVar<'a, 'tcx> {
    index: usize,
    ty: &'tcx Type<'tcx>,
    used: Cell<usize>,

    /// The initial value for immutable variable. `None` for mutable variable.
    value: Cell<Option<&'a Expr<'a, 'tcx>>>,

    /// `true` if this temporary variable can be updated.
    mutable: bool,
}

impl<'a, 'tcx> TmpVar<'a, 'tcx> {
    pub fn new(index: usize, ty: &'tcx Type<'tcx>, mutable: bool) -> Self {
        Self {
            index,
            ty,
            used: Cell::new(0),
            value: Cell::new(None),
            mutable,
        }
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }

    pub fn is_mutable(&self) -> bool {
        self.mutable
    }

    pub fn used(&self) -> usize {
        self.used.get()
    }

    pub fn value(&self) -> Option<&'a Expr<'a, 'tcx>> {
        self.value.get()
    }

    pub fn set_value(&self, value: &'a Expr<'a, 'tcx>) {
        self.value.set(Some(value));
    }

    pub fn inc_used(&self) -> usize {
        let u = self.used.get() + 1;
        self.used.set(u);
        u
    }

    pub fn reset_used(&self) {
        self.used.set(0);
    }

    pub fn dcr_used(&self) -> usize {
        let mut u = self.used.get();
        if u > 0 {
            u -= 1;
            self.used.set(u);
        }
        u
    }
}

impl fmt::Display for TmpVar<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.index)
    }
}

#[derive(Debug, Clone)]
pub struct TmpVarDef<'a, 'tcx> {
    var: &'a TmpVar<'a, 'tcx>,
    init: &'a Expr<'a, 'tcx>,
}

impl<'a, 'tcx> TmpVarDef<'a, 'tcx> {
    pub fn new(var: &'a TmpVar<'a, 'tcx>, init: &'a Expr<'a, 'tcx>) -> Self {
        Self { var, init }
    }

    pub fn with_init(&self, init: &'a Expr<'a, 'tcx>) -> Self {
        Self::new(self.var, init)
    }

    pub fn var(&self) -> &'a TmpVar<'a, 'tcx> {
        self.var
    }

    pub fn init(&self) -> &'a Expr<'a, 'tcx> {
        self.init
    }
}

impl fmt::Display for TmpVarDef<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.var.index)?;
        write!(f, "\t(used: {})", self.var.used.get())?;
        write!(f, " = {}", self.init,)
    }
}

#[derive(Debug, Clone)]
pub struct Phi<'a, 'tcx> {
    var: &'a TmpVar<'a, 'tcx>,
    value: &'a Expr<'a, 'tcx>,
}

impl<'a, 'tcx> Phi<'a, 'tcx> {
    pub fn new(var: &'a TmpVar<'a, 'tcx>, value: &'a Expr<'a, 'tcx>) -> Self {
        Self { var, value }
    }

    pub fn var(&self) -> &'a TmpVar<'a, 'tcx> {
        self.var
    }

    pub fn value(&self) -> &'a Expr<'a, 'tcx> {
        self.value
    }
}

impl fmt::Display for Phi<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "phi:t{}\t(used: {}) = {}",
            self.var.index,
            self.var.used.get(),
            self.value
        )
    }
}

#[derive(Debug, Clone)]
pub struct VarDef<'a, 'tcx> {
    name: String,
    init: &'a Expr<'a, 'tcx>,
}

impl<'a, 'tcx> VarDef<'a, 'tcx> {
    pub fn new(name: String, init: &'a Expr<'a, 'tcx>) -> Self {
        Self { name, init }
    }

    pub fn with_init(&self, init: &'a Expr<'a, 'tcx>) -> Self {
        Self {
            name: self.name.clone(),
            init,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn init(&self) -> &'a Expr<'a, 'tcx> {
        self.init
    }
}

impl fmt::Display for VarDef<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.name, self.init)
    }
}

#[derive(Debug, Clone)]
pub enum Stmt<'a, 'tcx> {
    // TODO: Can we unify TmpVar(Def) and Var(Def)?
    TmpVarDef(TmpVarDef<'a, 'tcx>),
    VarDef(VarDef<'a, 'tcx>),
    Cond(Cond<'a, 'tcx>),
    // "Phi" function for a basic block. This statement must appear at the end of
    // each branch.
    Phi(Phi<'a, 'tcx>),

    // "return" statement
    Ret(&'a Expr<'a, 'tcx>),
}

impl<'a, 'tcx> Stmt<'a, 'tcx> {
    pub fn tmp_var_def(var: &'a TmpVar<'a, 'tcx>, init: &'a Expr<'a, 'tcx>) -> Self {
        Self::TmpVarDef(TmpVarDef::new(var, init))
    }

    pub fn phi(var: &'a TmpVar<'a, 'tcx>, value: &'a Expr<'a, 'tcx>) -> Self {
        Self::Phi(Phi::new(var, value))
    }

    fn _fmt(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        write!(f, "{}", DISPLAY_INDENT.repeat(indent))?;
        match self {
            Stmt::TmpVarDef(def) => write!(f, "{}", def),
            Stmt::VarDef(def) => write!(f, "{}", def),
            Stmt::Ret(expr) => write!(f, "return {}", expr),
            Stmt::Phi(phi) => write!(f, "{}", phi),
            Stmt::Cond(cond) => cond._fmt(f, indent),
        }
    }
}

impl fmt::Display for Stmt<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self._fmt(f, 0)
    }
}

#[derive(Debug, Clone)]
pub struct Cond<'a, 'tcx> {
    /// The index of temporary variable which holds the result.
    pub var: &'a TmpVar<'a, 'tcx>,
    pub branches: Vec<Branch<'a, 'tcx>>,
}

impl<'a, 'tcx> Cond<'a, 'tcx> {
    fn _fmt(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        write!(f, "t{}\t(used: {}) = ", self.var.index, self.var.used())?;
        writeln!(f, "cond {{")?;
        for branch in &self.branches {
            branch._fmt(f, indent + 1)?;
            writeln!(f)?;
        }
        write!(f, "{}", DISPLAY_INDENT.repeat(indent))?;
        write!(f, "}}")
    }
}

impl fmt::Display for Cond<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self._fmt(f, 0)
    }
}

#[derive(Debug, Clone)]
pub struct Branch<'a, 'tcx> {
    pub condition: Option<&'a Expr<'a, 'tcx>>,
    pub body: Vec<&'a Stmt<'a, 'tcx>>,
}

impl<'a, 'tcx> Branch<'a, 'tcx> {
    fn _fmt(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        if let Some(condition) = self.condition {
            write!(f, "{}", DISPLAY_INDENT.repeat(indent))?;
            write!(f, "({}) => ", condition)?;
        }
        writeln!(f, "{{")?;

        for stmt in &self.body {
            stmt._fmt(f, indent + 1)?;
            writeln!(f)?;
        }
        write!(f, "{}", DISPLAY_INDENT.repeat(indent))?;
        write!(f, "}}")
    }
}

impl fmt::Display for Branch<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self._fmt(f, 0)
    }
}

#[derive(Debug, Clone)]
pub struct Expr<'a, 'tcx> {
    kind: ExprKind<'a, 'tcx>,
    ty: &'tcx Type<'tcx>,
}

impl<'a, 'tcx> Expr<'a, 'tcx> {
    pub fn usize(tcx: TypeContext<'tcx>, value: usize) -> Self {
        Self::int64(tcx, i64::try_from(value).unwrap())
    }
    pub fn int64(tcx: TypeContext<'tcx>, value: i64) -> Self {
        let kind = ExprKind::Int64(value);
        let ty = tcx.int64();

        Self::new(kind, ty)
    }
    pub fn bool(tcx: TypeContext<'tcx>, value: bool) -> Self {
        let kind = ExprKind::Bool(value);
        let ty = tcx.boolean();

        Self::new(kind, ty)
    }
    pub fn native_int(tcx: TypeContext<'tcx>, value: i64) -> Self {
        let kind = ExprKind::Int64(value);
        let ty = tcx.native_int();

        Self::new(kind, ty)
    }
    pub fn const_string(tcx: TypeContext<'tcx>, value: &str) -> Self {
        let kind = ExprKind::Str(value.to_string());
        let ty = tcx.string();

        Self::new(kind, ty)
    }
    pub fn tmp_var(tmp_var: &'a TmpVar<'a, 'tcx>) -> Self {
        let kind = ExprKind::TmpVar(tmp_var);
        Self::new(kind, tmp_var.ty())
    }
    pub fn not(tcx: TypeContext<'tcx>, operand: &'a Expr<'a, 'tcx>) -> Self {
        let kind = ExprKind::Not(operand);
        Self::new(kind, tcx.boolean())
    }
    pub fn eq(tcx: TypeContext<'tcx>, a: &'a Expr<'a, 'tcx>, b: &'a Expr<'a, 'tcx>) -> Self {
        let kind = ExprKind::Eq(a, b);
        Self::new(kind, tcx.boolean())
    }
    pub fn and(tcx: TypeContext<'tcx>, a: &'a Expr<'a, 'tcx>, b: &'a Expr<'a, 'tcx>) -> Self {
        let kind = ExprKind::And(a, b);
        Self::new(kind, tcx.boolean())
    }
    pub fn or(tcx: TypeContext<'tcx>, a: &'a Expr<'a, 'tcx>, b: &'a Expr<'a, 'tcx>) -> Self {
        let kind = ExprKind::Or(a, b);
        Self::new(kind, tcx.boolean())
    }
    pub fn ge(tcx: TypeContext<'tcx>, a: &'a Expr<'a, 'tcx>, b: &'a Expr<'a, 'tcx>) -> Self {
        let kind = ExprKind::Ge(a, b);
        Self::new(kind, tcx.boolean())
    }
    pub fn le(tcx: TypeContext<'tcx>, a: &'a Expr<'a, 'tcx>, b: &'a Expr<'a, 'tcx>) -> Self {
        let kind = ExprKind::Le(a, b);
        Self::new(kind, tcx.boolean())
    }
    pub fn gt(tcx: TypeContext<'tcx>, a: &'a Expr<'a, 'tcx>, b: &'a Expr<'a, 'tcx>) -> Self {
        let kind = ExprKind::Gt(a, b);
        Self::new(kind, tcx.boolean())
    }
    pub fn lt(tcx: TypeContext<'tcx>, a: &'a Expr<'a, 'tcx>, b: &'a Expr<'a, 'tcx>) -> Self {
        let kind = ExprKind::Lt(a, b);
        Self::new(kind, tcx.boolean())
    }
    pub fn printf(tcx: TypeContext<'tcx>, format_specs: Vec<FormatSpec<'a, 'tcx>>) -> Self {
        let kind = ExprKind::Printf(format_specs);
        Self::new(kind, tcx.int64())
    }
    pub fn union_tag(tcx: TypeContext<'tcx>, operand: &'a Expr<'a, 'tcx>) -> Self {
        assert!(matches!(operand.ty(), Type::Union(_)));
        let kind = ExprKind::UnionTag(operand);
        Self::new(kind, tcx.int64())
    }
    pub fn tuple_index_access(operand: &'a Expr<'a, 'tcx>, index: usize) -> Self {
        let tuple_ty = operand.ty().tuple_ty().expect("operand must be a tuple");
        assert!(index < tuple_ty.len());

        let kind = ExprKind::IndexAccess { operand, index };
        Self::new(kind, tuple_ty[index])
    }
    pub fn struct_field_access(operand: &'a Expr<'a, 'tcx>, name: &str) -> Self {
        let struct_ty = operand.ty().struct_ty().expect("operand must be a struct");
        let field = struct_ty
            .get_field(name)
            .unwrap_or_else(|| panic!("field {} not found", name));
        let kind = ExprKind::FieldAccess {
            operand,
            name: name.to_string(),
        };
        Self::new(kind, field.ty())
    }
    pub fn union_member_access(
        operand: &'a Expr<'a, 'tcx>,
        tag: usize,
        member_ty: &'tcx Type<'tcx>,
    ) -> Self {
        let kind = ExprKind::UnionMemberAccess { operand, tag };
        Self::new(kind, member_ty)
    }
    pub fn union_value(value: &'a Expr<'a, 'tcx>, tag: usize, union_ty: &'tcx Type<'tcx>) -> Self {
        let kind = ExprKind::UnionValue { value, tag };
        Self::new(kind, union_ty)
    }
    pub fn cond_value(
        cond: &'a Expr<'a, 'tcx>,
        then_value: &'a Expr<'a, 'tcx>,
        else_value: &'a Expr<'a, 'tcx>,
    ) -> Self {
        let then_ty = then_value.ty().bottom_ty();
        let else_ty = else_value.ty().bottom_ty();

        assert!(
            then_ty.is_compatible(else_ty),
            concat!(
                "conditional values must be compatible each other, but was `{}` and `{}`.",
                " then_value = {:#?}, else_value = {:#?}"
            ),
            then_ty,
            else_ty,
            then_value,
            else_value
        );

        let kind = ExprKind::CondValue {
            cond,
            then_value,
            else_value,
        };
        Self::new(kind, then_value.ty().bottom_ty())
    }

    pub fn new(kind: ExprKind<'a, 'tcx>, ty: &'tcx Type<'tcx>) -> Self {
        Self { kind, ty }
    }

    pub fn kind(&self) -> &ExprKind<'a, 'tcx> {
        &self.kind
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty.bottom_ty()
    }

    // Returns `true` if the expression is cheap operation, so it can
    // be used as immediate value.
    pub fn can_be_immediate(&self) -> bool {
        match &self.kind {
            ExprKind::Minus(a) | ExprKind::Not(a) => a.can_be_immediate(),
            ExprKind::Add(a, b)
            | ExprKind::Sub(a, b)
            | ExprKind::Mul(a, b)
            | ExprKind::Div(a, b)
            | ExprKind::Eq(a, b)
            | ExprKind::Ne(a, b)
            | ExprKind::Lt(a, b)
            | ExprKind::Le(a, b)
            | ExprKind::Gt(a, b)
            | ExprKind::Ge(a, b)
            | ExprKind::And(a, b)
            | ExprKind::Or(a, b) => a.can_be_immediate() && b.can_be_immediate(),
            ExprKind::CondValue { .. } => false,
            ExprKind::Tuple(_)
            | ExprKind::StructValue(_)
            | ExprKind::UnionValue { .. }
            | ExprKind::Call { .. }
            | ExprKind::Printf(_) => false,
            ExprKind::IndexAccess { operand, .. }
            | ExprKind::FieldAccess { operand, .. }
            | ExprKind::UnionTag(operand)
            | ExprKind::UnionMemberAccess { operand, .. } => operand.can_be_immediate(),
            ExprKind::Int64(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::TmpVar(_)
            | ExprKind::Var(_) => true,
            ExprKind::CondAndAssign { .. } => false,
        }
    }

    // Returns `true` if the expression can have side effects.
    pub fn has_side_effect(&self) -> bool {
        match &self.kind {
            ExprKind::Call { .. } | ExprKind::Printf(_) => true,
            ExprKind::Minus(a) | ExprKind::Not(a) => a.has_side_effect(),
            ExprKind::Add(a, b)
            | ExprKind::Sub(a, b)
            | ExprKind::Mul(a, b)
            | ExprKind::Div(a, b)
            | ExprKind::Eq(a, b)
            | ExprKind::Ne(a, b)
            | ExprKind::Lt(a, b)
            | ExprKind::Le(a, b)
            | ExprKind::Gt(a, b)
            | ExprKind::Ge(a, b)
            | ExprKind::And(a, b)
            | ExprKind::Or(a, b) => a.has_side_effect() || b.has_side_effect(),
            ExprKind::CondValue {
                cond,
                then_value,
                else_value,
            } => {
                cond.has_side_effect()
                    || then_value.has_side_effect()
                    || else_value.has_side_effect()
            }
            ExprKind::Tuple(fs) => fs.iter().any(|sub_expr| sub_expr.has_side_effect()),
            ExprKind::StructValue(fs) => fs.iter().any(|(_, sub_expr)| sub_expr.has_side_effect()),
            ExprKind::CondAndAssign { var: _, cond } => {
                if let Some(cond) = cond {
                    cond.has_side_effect()
                } else {
                    true
                }
            }
            ExprKind::Int64(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::IndexAccess { .. }
            | ExprKind::FieldAccess { .. }
            | ExprKind::UnionTag(_)
            | ExprKind::UnionMemberAccess { .. }
            | ExprKind::UnionValue { .. }
            | ExprKind::TmpVar(_)
            | ExprKind::Var(_) => false,
        }
    }
}

impl fmt::Display for Expr<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

#[derive(Debug, Clone)]
pub enum CallingConvention<'tcx> {
    /// C lang
    C,
    /// This lang
    Std(FunctionSignature<'tcx>),
}

#[derive(Debug, Clone)]
pub enum ExprKind<'a, 'tcx> {
    Minus(&'a Expr<'a, 'tcx>),
    Not(&'a Expr<'a, 'tcx>),
    Add(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Sub(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Mul(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Div(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Eq(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Ne(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Lt(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Le(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Gt(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Ge(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    And(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Or(&'a Expr<'a, 'tcx>, &'a Expr<'a, 'tcx>),
    Call {
        name: String,
        cc: CallingConvention<'tcx>,
        args: Vec<&'a Expr<'a, 'tcx>>,
    },
    CondValue {
        cond: &'a Expr<'a, 'tcx>,
        then_value: &'a Expr<'a, 'tcx>,
        else_value: &'a Expr<'a, 'tcx>,
    },
    /// Evaluate `cond` expression and assign a temporary variable with `true`.
    CondAndAssign {
        cond: Option<&'a Expr<'a, 'tcx>>,
        var: &'a TmpVar<'a, 'tcx>,
    },

    // Built-in procedures
    Printf(Vec<FormatSpec<'a, 'tcx>>),

    // Values
    Int64(i64),
    Bool(bool),
    Str(String),
    Tuple(Vec<&'a Expr<'a, 'tcx>>),
    StructValue(Vec<(String, &'a Expr<'a, 'tcx>)>),
    IndexAccess {
        operand: &'a Expr<'a, 'tcx>,
        index: usize,
    },
    FieldAccess {
        operand: &'a Expr<'a, 'tcx>,
        name: String,
    },
    TmpVar(&'a TmpVar<'a, 'tcx>),
    Var(Var<'tcx>),
    // -- Union type
    /// Get the tag of an union type.
    /// - The operand must be an union type value.
    /// - The return value is an int value. 0 =< n < the number of union members.
    UnionTag(&'a Expr<'a, 'tcx>),
    UnionMemberAccess {
        operand: &'a Expr<'a, 'tcx>,
        tag: usize,
    },
    /// Initialize an union value with `value` as initial value of
    /// tagged member.
    UnionValue {
        value: &'a Expr<'a, 'tcx>,
        tag: usize,
    },
}

impl fmt::Display for ExprKind<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprKind::Minus(a) => write!(f, "-{}", a),
            ExprKind::Not(a) => write!(f, "!{}", a),
            ExprKind::Add(a, b) => write!(f, "{} + {}", a, b),
            ExprKind::Sub(a, b) => write!(f, "{} - {}", a, b),
            ExprKind::Mul(a, b) => write!(f, "{} * {}", a, b),
            ExprKind::Div(a, b) => write!(f, "{} / {}", a, b),
            ExprKind::Eq(a, b) => write!(f, "{} == {}", a, b),
            ExprKind::Ne(a, b) => write!(f, "{} != {}", a, b),
            ExprKind::Lt(a, b) => write!(f, "{} < {}", a, b),
            ExprKind::Le(a, b) => write!(f, "{} <= {}", a, b),
            ExprKind::Gt(a, b) => write!(f, "{} > {}", a, b),
            ExprKind::Ge(a, b) => write!(f, "{} >= {}", a, b),
            ExprKind::And(a, b) => write!(f, "{} && {}", a, b),
            ExprKind::Or(a, b) => write!(f, "{} || {}", a, b),
            ExprKind::CondValue {
                cond,
                then_value,
                else_value,
            } => write!(f, "({} ? {} : {})", cond, then_value, else_value),
            ExprKind::CondAndAssign { var, cond } => {
                if let Some(cond) = cond {
                    write!(f, "{} && {} = true", cond, var)
                } else {
                    write!(f, "{} = true", var)
                }
            }
            ExprKind::Call { name, args, .. } => {
                write!(f, "{}", name)?;
                write!(f, "(")?;
                let mut it = args.iter().peekable();
                while let Some(a) = it.next() {
                    write!(f, "{}", a)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            ExprKind::Printf(args) => {
                write!(f, "@printf(")?;
                let mut it = args.iter().peekable();
                while let Some(a) = it.next() {
                    write!(f, "{}", a)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            ExprKind::Int64(i) => i.fmt(f),
            ExprKind::Bool(b) => b.fmt(f),
            ExprKind::Str(s) => write!(f, "\"{}\"", s.escape_default()),
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
            ExprKind::StructValue(fs) => {
                let mut it = fs.iter().peekable();
                let empty = it.peek().is_none();

                write!(f, "{{")?;
                if !empty {
                    write!(f, " ")?;
                }
                while let Some((name, value)) = it.next() {
                    write!(f, "{}: {}", name, value)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                if !empty {
                    write!(f, " ")?;
                }
                write!(f, "}}")
            }
            ExprKind::IndexAccess { operand, index } => write!(f, "{}.{}", operand, index),
            ExprKind::FieldAccess { operand, name } => write!(f, "{}.{}", operand, name),
            ExprKind::UnionTag(expr) => write!(f, "{}.tag", expr),
            ExprKind::UnionMemberAccess { operand, tag } => write!(f, "{}._u.{}", operand, tag),
            ExprKind::UnionValue { value: operand, .. } => write!(f, "(union){}", operand),
            ExprKind::TmpVar(var) => var.fmt(f),
            ExprKind::Var(var) => var.fmt(f),
        }
    }
}

#[derive(Debug, Clone)]
pub enum FormatSpec<'a, 'tcx> {
    Value(&'a Expr<'a, 'tcx>),
    /// Show value as `"{value}"`
    Quoted(&'a Expr<'a, 'tcx>),
    Str(&'static str),
}

impl fmt::Display for FormatSpec<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FormatSpec::Value(expr) => expr.fmt(f),
            FormatSpec::Quoted(expr) => {
                // expr should be already quoted
                expr.fmt(f)
            }
            FormatSpec::Str(s) => write!(f, "\"{}\"", s.escape_default()),
        }
    }
}
