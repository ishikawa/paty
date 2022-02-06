use crate::syntax::{self, PatternKind};
use crate::ty::{FunctionSignature, StructTy, Type, TypeContext, TypedField};
use std::cell::Cell;
use std::collections::HashSet;
use std::fmt;
use typed_arena::Arena;

#[derive(Debug, Default)]
pub struct Program<'a, 'tcx> {
    decl_types: Vec<&'tcx Type<'tcx>>,
    functions: Vec<Function<'a, 'tcx>>,
}

impl<'a, 'tcx> Program<'a, 'tcx> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_decl_type(&mut self, ty: &'tcx Type<'tcx>) {
        if self.decl_types.contains(&ty) {
            return;
        }

        // To follow forward declaration rule, add field types first.
        match ty {
            Type::Tuple(fs) => {
                for fty in fs.iter() {
                    self.add_decl_type(fty);
                }
            }
            Type::Struct(struct_ty) => {
                for f in struct_ty.fields() {
                    self.add_decl_type(f.ty());
                }
            }
            Type::Int64 | Type::Boolean | Type::String | Type::NativeInt => {
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

    pub fn functions(&self) -> impl Iterator<Item = &Function<'a, 'tcx>> {
        self.functions.iter()
    }
}

impl fmt::Display for Program<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for fun in &self.functions {
            write!(f, "{}", fun)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Function<'a, 'tcx> {
    pub name: String,
    pub params: Vec<Parameter<'a, 'tcx>>,
    pub signature: FunctionSignature<'tcx>,
    pub body: Vec<Stmt<'a, 'tcx>>,
    pub retty: &'tcx Type<'tcx>,
    /// Whether this function is `main` or not.
    pub is_entry_point: bool,
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
                writeln!(f, "  {}", line)?;
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
    pub index: usize,
    pub ty: &'tcx Type<'tcx>,
    pub used: Cell<usize>,
    pub immediate: Cell<Option<&'a Expr<'a, 'tcx>>>,
}

impl<'a, 'tcx> TmpVar<'a, 'tcx> {
    pub fn new(index: usize, ty: &'tcx Type<'tcx>) -> Self {
        Self {
            index,
            ty,
            used: Cell::new(0),
            immediate: Cell::new(None),
        }
    }
}

impl fmt::Display for TmpVar<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.index)
    }
}

#[derive(Debug)]
pub enum Stmt<'a, 'tcx> {
    // TODO: Can we unify TmpVar(Def) and Var(Def)?
    TmpVarDef {
        var: &'a TmpVar<'a, 'tcx>,
        init: &'a Expr<'a, 'tcx>,
        pruned: Cell<bool>,
    },
    VarDef {
        name: String,
        init: &'a Expr<'a, 'tcx>,
    },
    Cond {
        /// The index of temporary variable which holds the result.
        var: &'a TmpVar<'a, 'tcx>,
        branches: Vec<Branch<'a, 'tcx>>,
    },
    // "Phi" function for a basic block. This statement must appear at the end of
    // each branch.
    Phi {
        var: &'a TmpVar<'a, 'tcx>,
        value: &'a Expr<'a, 'tcx>,
        pruned: Cell<bool>,
    },
    // "return" statement
    Ret(&'a Expr<'a, 'tcx>),
}

impl fmt::Display for Stmt<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::TmpVarDef { var, init, pruned } => {
                write!(
                    f,
                    "t{} (used: {}, pruned: {}) = {:?}",
                    var.index,
                    var.used.get(),
                    pruned.get(),
                    init
                )?;
            }
            Stmt::VarDef { name, init } => {
                write!(f, "{} = {:?}", name, init)?;
            }
            Stmt::Ret(expr) => {
                write!(f, "return {:?}", expr)?;
            }
            Stmt::Phi { var, value, pruned } => {
                write!(
                    f,
                    "phi(t{} (used: {}, pruned: {}) = {:?})",
                    var.index,
                    var.used.get(),
                    pruned.get(),
                    value
                )?;
            }
            Stmt::Cond { var: ret, branches } => {
                write!(f, "t{} (used: {}) = ", ret.index, ret.used.get())?;
                writeln!(f, "cond {{")?;
                for branch in branches {
                    writeln!(f, "  {:?}", branch)?;
                }
                write!(f, "}}")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Branch<'a, 'tcx> {
    pub condition: Option<&'a Expr<'a, 'tcx>>,
    pub body: Vec<Stmt<'a, 'tcx>>,
}

#[derive(Debug)]
pub struct Expr<'a, 'tcx> {
    kind: ExprKind<'a, 'tcx>,
    ty: &'tcx Type<'tcx>,
}

impl<'a, 'tcx> Expr<'a, 'tcx> {
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
            ExprKind::Add(_, _)
            | ExprKind::Sub(_, _)
            | ExprKind::Mul(_, _)
            | ExprKind::Div(_, _)
            | ExprKind::Eq(_, _)
            | ExprKind::Ne(_, _)
            | ExprKind::Lt(_, _)
            | ExprKind::Le(_, _)
            | ExprKind::Gt(_, _)
            | ExprKind::Ge(_, _)
            | ExprKind::And(_, _)
            | ExprKind::Or(_, _) => false,
            ExprKind::Tuple(_)
            | ExprKind::StructValue(_)
            | ExprKind::Call { .. }
            | ExprKind::Printf(_) => false,
            ExprKind::Int64(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::IndexAccess { .. }
            | ExprKind::FieldAccess { .. }
            | ExprKind::TmpVar(_)
            | ExprKind::Var(_) => true,
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
            ExprKind::Tuple(fs) => fs.iter().any(|sub_expr| sub_expr.has_side_effect()),
            ExprKind::StructValue(fs) => fs.iter().any(|(_, sub_expr)| sub_expr.has_side_effect()),
            ExprKind::Int64(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::IndexAccess { .. }
            | ExprKind::FieldAccess { .. }
            | ExprKind::TmpVar(_)
            | ExprKind::Var(_) => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum CallingConvention<'tcx> {
    /// C lang
    C,
    /// This lang
    Std(FunctionSignature<'tcx>),
}

#[derive(Debug)]
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
}

#[derive(Debug, Clone)]
pub enum FormatSpec<'a, 'tcx> {
    Value(&'a Expr<'a, 'tcx>),
    /// Show value as `"{value}"`
    Quoted(&'a Expr<'a, 'tcx>),
    Str(&'static str),
}

pub struct Builder<'a, 'tcx> {
    tcx: TypeContext<'tcx>,
    /// An arena allocators for nodes.
    expr_arena: &'a Arena<Expr<'a, 'tcx>>,
    tmp_var_arena: &'a Arena<TmpVar<'a, 'tcx>>,
    /// The current index of temporary variables. It starts from 0 and
    /// incremented by creating a new temporary variable. This index will
    /// be saved and reset to 0 when function enter, and restored when function exit.
    tmp_var_index: usize,
}

impl<'a, 'nd: 'tcx, 'tcx> Builder<'a, 'tcx> {
    pub fn new(
        tcx: TypeContext<'tcx>,
        expr_arena: &'a Arena<Expr<'a, 'tcx>>,
        tmp_var_arena: &'a Arena<TmpVar<'a, 'tcx>>,
    ) -> Self {
        Self {
            tcx,
            expr_arena,
            tmp_var_arena,
            tmp_var_index: 0,
        }
    }

    pub fn build(&mut self, ast: &'nd [syntax::TopLevel<'nd, 'tcx>]) -> Program<'a, 'tcx> {
        let mut program = Program::new();
        let mut stmts = vec![];

        // Build top level statements and function definitions.
        for top_level in ast {
            match top_level {
                syntax::TopLevel::Declaration(decl) => {
                    self._build_decl(decl, &mut program, &mut stmts);
                }
                syntax::TopLevel::Stmt(stmt) => {
                    self._build_stmt(stmt, &mut program, &mut stmts);
                }
            }
        }

        // Add `return 0` statement for the entry point function if needed.
        if !matches!(stmts.last(), Some(Stmt::Ret(_))) {
            stmts.push(Stmt::Ret(self.native_int(0)))
        }

        let signature = FunctionSignature::new("main".to_string(), vec![]);
        let main = Function {
            name: "main".to_string(),
            params: vec![],
            signature,
            body: stmts,
            retty: self.tcx.native_int(),
            is_entry_point: true,
        };
        program.functions.push(main);

        // post process
        let mut optimizer = Optimizer::new();
        optimizer.optimize(&mut program);

        program
    }

    fn next_temp_var(&mut self, ty: &'tcx Type<'tcx>) -> &'a TmpVar<'a, 'tcx> {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        self.tmp_var_arena.alloc(TmpVar::new(t, ty))
    }

    fn push_expr(
        &mut self,
        expr: &'a Expr<'a, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let t = self.next_temp_var(expr.ty());
        let stmt = Stmt::TmpVarDef {
            var: t,
            init: expr,
            pruned: Cell::new(false),
        };
        stmts.push(stmt);

        let kind = ExprKind::TmpVar(t);
        self.expr_arena.alloc(Expr::new(kind, expr.ty()))
    }

    fn push_expr_kind(
        &mut self,
        kind: ExprKind<'a, 'tcx>,
        expr_ty: &'tcx Type<'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let expr = self.expr_arena.alloc(Expr::new(kind, expr_ty));
        let t = self.next_temp_var(expr.ty());
        let stmt = Stmt::TmpVarDef {
            var: t,
            init: expr,
            pruned: Cell::new(false),
        };
        stmts.push(stmt);

        let kind = ExprKind::TmpVar(t);
        self.expr_arena.alloc(Expr::new(kind, expr.ty()))
    }

    fn int64(&self, value: i64) -> &'a Expr<'a, 'tcx> {
        let kind = ExprKind::Int64(value);
        let ty = self.tcx.int64();

        self.expr_arena.alloc(Expr::new(kind, ty))
    }

    fn native_int(&self, value: i64) -> &'a Expr<'a, 'tcx> {
        let kind = ExprKind::Int64(value);
        let ty = self.tcx.native_int();

        self.expr_arena.alloc(Expr::new(kind, ty))
    }

    #[allow(unused)]
    fn bool(&self, value: bool) -> &'a Expr<'a, 'tcx> {
        let kind = ExprKind::Bool(value);
        let ty = self.tcx.boolean();

        self.expr_arena.alloc(Expr::new(kind, ty))
    }

    fn const_string(&self, value: &str) -> &'a Expr<'a, 'tcx> {
        let kind = ExprKind::Str(value.to_string());
        let ty = self.tcx.string();

        self.expr_arena.alloc(Expr::new(kind, ty))
    }

    fn _build_decl(
        &mut self,
        decl: &syntax::Declaration<'nd, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        _stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) {
        match decl.kind() {
            syntax::DeclarationKind::Function(syntax_fun) => {
                // save and reset temp var index
                let saved_tmp_var_index = self.tmp_var_index;
                self.tmp_var_index = 0;

                // convert parameter pattern to parameter name and assign variable.
                let mut params = vec![];
                let mut body_stmts = vec![];

                for p in syntax_fun.params() {
                    let pat = p.pattern();
                    let ty = pat.expect_ty();

                    // To emit anonymous struct type
                    program.add_decl_type(ty);

                    // Assign parameter names to be able to referenced later.
                    let param = match pat.kind() {
                        PatternKind::Var(name) => Parameter::Var(Var::new(name, ty)),
                        PatternKind::Wildcard => {
                            // ignore pattern but we have to define a parameter.
                            Parameter::TmpVar(self.next_temp_var(ty))
                        }
                        PatternKind::Tuple(_) | PatternKind::Struct(_) => {
                            // Create a temporary parameter name to be able to referenced in the body.
                            // Simultaneously, we build deconstruct assignment expressions.
                            let t = self.next_temp_var(ty);
                            let param_expr =
                                self.expr_arena.alloc(Expr::new(ExprKind::TmpVar(t), ty));

                            self._build_let_pattern(pat, param_expr, program, &mut body_stmts);

                            Parameter::TmpVar(t)
                        }
                        PatternKind::Integer(_)
                        | PatternKind::Boolean(_)
                        | PatternKind::String(_)
                        | PatternKind::Range { .. }
                        | PatternKind::Or(..) => {
                            unreachable!("Unsupported let pattern: `{}`", p.pattern().kind());
                        }
                    };

                    params.push(param);
                }

                // return
                let mut ret = None;
                for stmt in syntax_fun.body() {
                    ret = self._build_stmt(stmt, program, &mut body_stmts);
                }
                if let Some(ret) = ret {
                    body_stmts.push(Stmt::Ret(inc_used(ret)));
                }

                // Return type of the function
                let retty = syntax_fun.retty().unwrap_or_else(|| self.tcx.unit());

                let fun = Function {
                    name: syntax_fun.name().to_string(),
                    params,
                    signature: syntax_fun.signature(),
                    body: body_stmts,
                    retty,
                    is_entry_point: false,
                };
                program.functions.push(fun);

                // restore
                self.tmp_var_index = saved_tmp_var_index;
            }
            syntax::DeclarationKind::Struct(struct_def) => {
                program.add_decl_type(struct_def.ty());
            }
        }
    }

    fn _build_stmt(
        &mut self,
        stmt: &syntax::Stmt<'nd, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        match stmt.kind() {
            syntax::StmtKind::Let { pattern, rhs } => {
                let init = self._build_expr(rhs, program, stmts);
                self._build_let_pattern(pattern, init, program, stmts);

                None
            }
            syntax::StmtKind::Expr(expr) => {
                let value = self._build_expr(expr, program, stmts);
                Some(value)
            }
        }
    }

    fn _build_expr(
        &mut self,
        expr: &'nd syntax::Expr<'nd, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        match expr.kind() {
            syntax::ExprKind::Integer(n) => {
                let kind = ExprKind::Int64(*n);
                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Boolean(b) => {
                let kind = ExprKind::Bool(*b);
                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::String(s) => {
                let expr = self.const_string(s);
                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Tuple(sub_exprs) => {
                // Add tuple type to declaration types, because we have to
                // declare tuple type as a struct type in C.
                // However, the Zero-sized struct should not have a definition.
                let tuple_ty = expr.expect_ty();
                program.add_decl_type(tuple_ty);

                let mut values = vec![];

                for sub in sub_exprs {
                    let value = self._build_expr(sub, program, stmts);
                    values.push(inc_used(value));
                }

                let kind = ExprKind::Tuple(values);
                self.push_expr_kind(kind, tuple_ty, stmts)
            }
            syntax::ExprKind::Struct(struct_value) => {
                if struct_value.name().is_none() {
                    // Add anonymous struct type to declaration types, because we have to
                    // declare a type as a struct type in C.
                    // However, the Zero-sized struct should not have a definition.
                    program.add_decl_type(expr.expect_ty());
                }

                // Latter initializer can override previous initializers.
                // So generate initializer values in reversed order.
                let mut value_fields = vec![];
                let mut initialized_fields = HashSet::new();

                for field_or_spread in struct_value.fields().iter().rev() {
                    match field_or_spread {
                        syntax::ValueFieldOrSpread::ValueField(field) => {
                            if !initialized_fields.contains(&field.name()) {
                                let value = self._build_expr(field.value(), program, stmts);
                                value_fields.push((field.name().to_string(), inc_used(value)));
                                initialized_fields.insert(field.name());
                            }
                        }
                        syntax::ValueFieldOrSpread::Spread(spread) => {
                            let operand = spread.expect_operand();
                            let fields = match operand.expect_ty() {
                                Type::Struct(struct_ty) => struct_ty.fields(),
                                _ => unreachable!("spread with invalid expr: {}", spread),
                            };
                            let built_spread_value = None;
                            for field in fields.iter().rev() {
                                if initialized_fields.contains(&field.name()) {
                                    // Overridden
                                    continue;
                                }

                                let spread_value = built_spread_value
                                    .unwrap_or_else(|| self._build_expr(operand, program, stmts));

                                let kind = ExprKind::FieldAccess {
                                    name: field.name().to_string(),
                                    operand: inc_used(spread_value),
                                };
                                let expr = self.expr_arena.alloc(Expr::new(kind, field.ty()));
                                value_fields.push((field.name().to_string(), inc_used(expr)));
                                initialized_fields.insert(field.name());
                            }
                        }
                    }
                }

                // Reversed -> Ordered
                value_fields.reverse();

                let kind = ExprKind::StructValue(value_fields);
                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Minus(a) => {
                let a = self._build_expr(a, program, stmts);
                let kind = ExprKind::Minus(inc_used(a));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Add(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Add(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Sub(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Sub(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Mul(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Mul(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Div(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Div(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Eq(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Eq(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Ne(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Ne(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Lt(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Lt(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Gt(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Gt(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Le(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Le(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Ge(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Ge(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::And(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::And(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Or(a, b) => {
                let a = self._build_expr(a, program, stmts);
                let b = self._build_expr(b, program, stmts);
                let kind = ExprKind::Or(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Var(name) => {
                let kind = ExprKind::Var(Var::new(name, expr.expect_ty()));
                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::IndexAccess(operand, index) => {
                let operand = self._build_expr(operand, program, stmts);
                let kind = ExprKind::IndexAccess {
                    operand: inc_used(operand),
                    index: *index,
                };

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::FieldAccess(operand, name) => {
                let operand = self._build_expr(operand, program, stmts);
                let kind = ExprKind::FieldAccess {
                    operand: inc_used(operand),
                    name: name.to_string(),
                };

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Call(call_expr) => {
                // The type of call expression can be not yet inferred due to
                // forward declaration.
                let expr_ty = if let Some(syntax_fun) = call_expr.function() {
                    syntax_fun.retty().unwrap_or_else(|| self.tcx.unit())
                } else if let Some(expr_ty) = expr.ty() {
                    expr_ty
                } else {
                    unreachable!(
                        "Semantic analyzer couldn't assign type for call expression: {:?}",
                        call_expr
                    );
                };

                let sig = call_expr.function().unwrap().signature();
                let kind = ExprKind::Call {
                    name: call_expr.name().to_string(),
                    cc: CallingConvention::Std(sig),
                    args: call_expr
                        .arguments()
                        .iter()
                        .map(|a| {
                            let a = self._build_expr(a, program, stmts);
                            inc_used(a)
                        })
                        .collect(),
                };

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Puts(args) => {
                // Generates `printf(...)` code for `puts(...)`.
                let mut format_specs = vec![];

                // Build format specifiers
                let mut it = args.iter().peekable();

                while let Some(arg) = it.next() {
                    let a = self._build_expr(arg, program, stmts);
                    self._printf_format(a, program, stmts, &mut format_specs, false);

                    // separated by a space
                    if it.peek().is_some() {
                        format_specs.push(FormatSpec::Str(" "));
                    }
                }
                format_specs.push(FormatSpec::Str("\n"));

                // Build arguments
                let kind = ExprKind::Printf(format_specs);
                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Case {
                head,
                arms,
                else_body,
            } => {
                let t = self.next_temp_var(expr.ty().unwrap());
                let t_head = self._build_expr(head, program, stmts);

                // Construct "if-else" statement from each branches.
                let mut branches = arms
                    .iter()
                    .map(|arm| {
                        // Build an condition and variable declarations from the pattern
                        let mut branch_stmts = vec![];
                        let condition =
                            self._build_pattern(t_head, arm.pattern(), program, &mut branch_stmts);
                        let ret = self._build_expr(arm.body(), program, &mut branch_stmts);

                        branch_stmts.push(Stmt::Phi {
                            var: t,
                            value: inc_used(ret),
                            pruned: Cell::new(false),
                        });

                        Branch {
                            condition,
                            body: branch_stmts,
                        }
                    })
                    .collect::<Vec<_>>();

                if let Some(else_body) = else_body {
                    let mut branch_stmts = vec![];
                    let ret = self._build_expr(else_body, program, &mut branch_stmts);
                    branch_stmts.push(Stmt::Phi {
                        var: t,
                        value: inc_used(ret),
                        pruned: Cell::new(false),
                    });

                    let branch = Branch {
                        condition: None,
                        body: branch_stmts,
                    };
                    branches.push(branch);
                } else if !branches.is_empty() {
                    // No explicit `else` arm for this `case` expression. However,
                    // the last arm of every `case` expression which was passed through usefulness check can
                    // be `else` arm.
                    let i = branches.len() - 1;
                    branches[i].condition = None;
                }

                let stmt = Stmt::Cond { branches, var: t };
                stmts.push(stmt);

                let kind = ExprKind::TmpVar(t);
                self.expr_arena.alloc(Expr::new(kind, t.ty))
            }
        }
    }

    fn _printf_format(
        &mut self,
        arg: &'a Expr<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
        specs: &mut Vec<FormatSpec<'a, 'tcx>>,
        escape_string: bool,
    ) {
        match arg.ty() {
            Type::Int64 | Type::NativeInt | Type::Boolean => {
                specs.push(FormatSpec::Value(inc_used(arg)));
            }
            Type::String => {
                if escape_string {
                    specs.push(FormatSpec::Quoted(inc_used(arg)));
                } else {
                    specs.push(FormatSpec::Value(inc_used(arg)));
                }
            }
            Type::Tuple(fs) => {
                let mut it = fs.iter().enumerate().peekable();

                specs.push(FormatSpec::Str("("));
                while let Some((i, sub_ty)) = it.next() {
                    let kind = ExprKind::IndexAccess {
                        operand: inc_used(arg),
                        index: i,
                    };

                    let ir_expr = self.push_expr_kind(kind, sub_ty, stmts);
                    self._printf_format(ir_expr, program, stmts, specs, true);

                    if it.peek().is_some() {
                        specs.push(FormatSpec::Str(", "));
                    }
                }
                specs.push(FormatSpec::Str(")"));
            }
            Type::Struct(struct_ty) => {
                if let Some(name) = struct_ty.name() {
                    specs.push(FormatSpec::Value(self.const_string(name)));
                    specs.push(FormatSpec::Str(" "));
                }
                self._printf_format_typed_fields(arg, struct_ty.fields(), program, stmts, specs);
            }
            Type::Named(name) => unreachable!("untyped for the type named: {}", name),
            Type::Undetermined => unreachable!("untyped code"),
        }
    }

    fn _printf_format_typed_fields(
        &mut self,
        arg: &'a Expr<'a, 'tcx>,
        fields: &[TypedField<'tcx>],
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
        specs: &mut Vec<FormatSpec<'a, 'tcx>>,
    ) {
        let mut it = fields.iter().peekable();
        let empty = it.peek().is_none();
        specs.push(FormatSpec::Str("{"));
        if !empty {
            specs.push(FormatSpec::Str(" "));
        }

        while let Some(f) = it.next() {
            specs.push(FormatSpec::Value(self.const_string(f.name())));
            specs.push(FormatSpec::Str(": "));

            let kind = ExprKind::FieldAccess {
                operand: inc_used(arg),
                name: f.name().to_string(),
            };

            let ir_expr = self.push_expr_kind(kind, f.ty(), stmts);
            self._printf_format(ir_expr, program, stmts, specs, true);

            if it.peek().is_some() {
                specs.push(FormatSpec::Str(", "));
            }
        }

        if !empty {
            specs.push(FormatSpec::Str(" "));
        }
        specs.push(FormatSpec::Str("}"));
    }

    // Returns `None` for no condition.
    fn _build_pattern(
        &mut self,
        t_expr: &'a Expr<'a, 'tcx>,
        pat: &'nd syntax::Pattern<'nd, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        // zero-sized type is always matched with a value.
        if pat.expect_ty().is_zero_sized() {
            return None;
        }

        match pat.kind() {
            PatternKind::Integer(n) => {
                let value = self.int64(*n);
                let eq = ExprKind::Eq(inc_used(t_expr), value);

                let expr = self.expr_arena.alloc(Expr::new(eq, self.tcx.boolean()));
                Some(expr)
            }
            PatternKind::Boolean(b) => {
                let expr = if *b {
                    inc_used(t_expr)
                } else {
                    let expr = ExprKind::Not(inc_used(t_expr));
                    self.expr_arena.alloc(Expr::new(expr, self.tcx.boolean()))
                };
                Some(expr)
            }
            PatternKind::String(s) => {
                // Compare the value of head expression and pattern string with
                // POSIX `strcmp` function.
                let value = self.const_string(s);
                let kind = ExprKind::Call {
                    name: "strcmp".to_string(),
                    cc: CallingConvention::C,
                    args: vec![inc_used(t_expr), value],
                };
                let strcmp = self.expr_arena.alloc(Expr::new(kind, self.tcx.int64()));

                let zero = self.native_int(0);
                let eq = ExprKind::Eq(inc_used(strcmp), zero);

                let expr = self.expr_arena.alloc(Expr::new(eq, self.tcx.boolean()));
                Some(expr)
            }
            PatternKind::Range { lo, hi, end } => {
                let lo = self.int64(*lo);
                let hi = self.int64(*hi);

                let lhs = ExprKind::Ge(inc_used(t_expr), lo);

                let rhs = match end {
                    syntax::RangeEnd::Included => ExprKind::Le(inc_used(t_expr), hi),
                    syntax::RangeEnd::Excluded => ExprKind::Lt(inc_used(t_expr), hi),
                };

                let kind = ExprKind::And(
                    self.expr_arena.alloc(Expr::new(lhs, self.tcx.boolean())),
                    self.expr_arena.alloc(Expr::new(rhs, self.tcx.boolean())),
                );

                let expr = self.expr_arena.alloc(Expr::new(kind, self.tcx.boolean()));
                Some(expr)
            }
            PatternKind::Tuple(sub_pats) => {
                if sub_pats.is_empty() {
                    unreachable!(
                        "Empty tuple must be zero-sized type. It should be handled above."
                    );
                } else {
                    let kind = ExprKind::IndexAccess {
                        operand: inc_used(t_expr),
                        index: 0,
                    };
                    let operand = self
                        .expr_arena
                        .alloc(Expr::new(kind, sub_pats[0].expect_ty()));

                    let mut condition = self._build_pattern(operand, sub_pats[0], program, stmts);

                    for (i, pat) in sub_pats.iter().enumerate().skip(1) {
                        let kind = ExprKind::IndexAccess {
                            operand: inc_used(t_expr),
                            index: i,
                        };
                        let operand = self.expr_arena.alloc(Expr::new(kind, pat.expect_ty()));
                        let sub_condition = self._build_pattern(operand, pat, program, stmts);

                        if let Some(cond) = condition {
                            if let Some(sub_cond) = sub_condition {
                                let kind = ExprKind::And(cond, sub_cond);
                                condition = Some(
                                    self.expr_arena.alloc(Expr::new(kind, self.tcx.boolean())),
                                );
                            }
                        } else {
                            condition = sub_condition;
                        }
                    }

                    condition
                }
            }
            PatternKind::Struct(struct_pat) => {
                if struct_pat.fields().len() == 0 {
                    unreachable!(
                        "Empty struct must be zero-sized type. It should be handled above."
                    );
                } else {
                    // Split fields into pattern fields and a spread.
                    let mut pattern_fields = vec![];
                    let mut spread_pat = None;

                    for f in struct_pat.fields() {
                        match f {
                            syntax::PatternFieldOrSpread::PatternField(pf) => {
                                pattern_fields.push(pf);
                            }
                            syntax::PatternFieldOrSpread::Spread(spread) => {
                                spread_pat = Some(spread);
                            }
                        }
                    }
                    if let Some(spread_pat) = spread_pat {
                        if let Some(spread_name) = spread_pat.name() {
                            let spread_ty = spread_pat.expect_ty();
                            program.add_decl_type(spread_ty);

                            let struct_ty = spread_pat.expect_struct_ty();
                            let values = self.struct_values(struct_ty, t_expr);
                            let struct_value = self
                                .expr_arena
                                .alloc(Expr::new(ExprKind::StructValue(values), spread_ty));

                            stmts.push(Stmt::VarDef {
                                name: spread_name.to_string(),
                                init: inc_used(struct_value),
                            });
                        }
                    }

                    // no condition
                    if pattern_fields.is_empty() {
                        return None;
                    }

                    let first_field = pattern_fields[0];
                    let kind = ExprKind::FieldAccess {
                        operand: inc_used(t_expr),
                        name: first_field.name().to_string(),
                    };
                    let operand = self
                        .expr_arena
                        .alloc(Expr::new(kind, first_field.pattern().expect_ty()));

                    let mut condition =
                        self._build_pattern(operand, first_field.pattern(), program, stmts);

                    for pat_field in pattern_fields.iter().skip(1) {
                        let kind = ExprKind::FieldAccess {
                            operand: inc_used(t_expr),
                            name: pat_field.name().to_string(),
                        };
                        let operand = self
                            .expr_arena
                            .alloc(Expr::new(kind, pat_field.pattern().expect_ty()));
                        let sub_condition =
                            self._build_pattern(operand, pat_field.pattern(), program, stmts);

                        if let Some(cond) = condition {
                            if let Some(sub_cond) = sub_condition {
                                let kind = ExprKind::And(cond, sub_cond);
                                condition = Some(
                                    self.expr_arena.alloc(Expr::new(kind, self.tcx.boolean())),
                                );
                            }
                        } else {
                            condition = sub_condition;
                        }
                    }

                    condition
                }
            }
            PatternKind::Var(name) => {
                stmts.push(Stmt::VarDef {
                    name: name.clone(),
                    init: inc_used(t_expr),
                });

                None
            }
            PatternKind::Or(..) => todo!(),
            PatternKind::Wildcard => None,
        }
    }

    fn _build_let_pattern(
        &mut self,
        pattern: &'nd syntax::Pattern<'nd, 'tcx>,
        init: &'a Expr<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) {
        match pattern.kind() {
            PatternKind::Var(name) => {
                let stmt = Stmt::VarDef {
                    name: name.to_string(),
                    init: inc_used(init),
                };
                stmts.push(stmt);
            }
            PatternKind::Wildcard => {
                // no bound variable to `_`
            }
            PatternKind::Tuple(fs) => {
                for (i, sub_pat) in fs.iter().enumerate() {
                    let kind = ExprKind::IndexAccess {
                        operand: inc_used(init),
                        index: i,
                    };
                    let field = self.expr_arena.alloc(Expr::new(kind, sub_pat.expect_ty()));

                    self._build_let_pattern(sub_pat, field, program, stmts)
                }
            }
            PatternKind::Struct(struct_pat) => {
                for f in struct_pat.fields() {
                    match f {
                        syntax::PatternFieldOrSpread::PatternField(pat_field) => {
                            let kind = ExprKind::FieldAccess {
                                operand: inc_used(init),
                                name: pat_field.name().to_string(),
                            };
                            let field = self
                                .expr_arena
                                .alloc(Expr::new(kind, pat_field.pattern().expect_ty()));

                            self._build_let_pattern(pat_field.pattern(), field, program, stmts)
                        }
                        syntax::PatternFieldOrSpread::Spread(spread_pat) => {
                            if let Some(spread_name) = spread_pat.name() {
                                let spread_ty = spread_pat.expect_ty();
                                program.add_decl_type(spread_ty);

                                let struct_ty = spread_pat.expect_struct_ty();
                                let values = self.struct_values(struct_ty, init);
                                let struct_value = self
                                    .expr_arena
                                    .alloc(Expr::new(ExprKind::StructValue(values), spread_ty));

                                stmts.push(Stmt::VarDef {
                                    name: spread_name.to_string(),
                                    init: inc_used(struct_value),
                                });
                            }
                        }
                    }
                }
            }
            PatternKind::Integer(_)
            | PatternKind::Boolean(_)
            | PatternKind::String(_)
            | PatternKind::Range { .. }
            | PatternKind::Or(..) => {
                unreachable!("Unsupported let pattern: `{}`", pattern.kind());
            }
        };
    }

    fn struct_values(
        &self,
        struct_ty: &StructTy<'tcx>,
        init: &'a Expr<'a, 'tcx>,
    ) -> Vec<(String, &'a Expr<'a, 'tcx>)> {
        struct_ty
            .fields()
            .iter()
            .map(|f| {
                let kind = ExprKind::FieldAccess {
                    operand: inc_used(init),
                    name: f.name().to_string(),
                };
                let v = self.expr_arena.alloc(Expr::new(kind, f.ty()));

                (f.name().to_string(), &*v)
            })
            .collect::<Vec<_>>()
    }
}

#[derive(Default, Debug)]
pub struct Optimizer {}

impl<'a, 'tcx> Optimizer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn optimize(&mut self, program: &mut Program<'a, 'tcx>) {
        for fun in &mut program.functions {
            self.optimize_function(fun);
        }
    }

    fn optimize_function(&mut self, fun: &Function<'a, 'tcx>) {
        for stmt in &fun.body {
            self.optimize_stmt(stmt);
        }
    }

    fn optimize_stmt(&mut self, stmt: &Stmt<'a, 'tcx>) {
        match stmt {
            Stmt::TmpVarDef { var, init, pruned } => {
                if var.used.get() == 1 || init.can_be_immediate() {
                    // This temporary variable is used only once, so it could be
                    // replaced with the expression.
                    var.immediate.set(Some(init));
                    pruned.set(true);
                    return;
                }
                self.optimize_expr(init);
            }
            Stmt::VarDef { init, .. } => {
                self.optimize_expr(init);
            }
            Stmt::Ret(expr) => {
                self.optimize_expr(expr);
            }
            Stmt::Phi { var, value, pruned } => {
                if var.used.get() == 0 {
                    // The result of cond expression is unused.
                    // So decrement the used count of a value because we increment it in
                    // Builder::build().
                    if dcr_used_and_prunable(value) {
                        pruned.set(true);
                        return;
                    }
                }

                self.optimize_expr(value);
            }
            Stmt::Cond { branches, .. } => {
                // Construct "if-else" statement from each branches.
                for branch in branches {
                    if let Some(condition) = branch.condition {
                        self.optimize_expr(condition);
                    }

                    // body
                    for stmt in &branch.body {
                        self.optimize_stmt(stmt);
                    }
                }
            }
        }
    }

    fn optimize_expr(&mut self, expr: &Expr<'a, 'tcx>) {
        match expr.kind() {
            ExprKind::Minus(operand) | ExprKind::Not(operand) => {
                self.optimize_expr(operand);
            }
            ExprKind::Add(lhs, rhs)
            | ExprKind::Sub(lhs, rhs)
            | ExprKind::Mul(lhs, rhs)
            | ExprKind::Div(lhs, rhs)
            | ExprKind::Eq(lhs, rhs)
            | ExprKind::Ne(lhs, rhs)
            | ExprKind::Lt(lhs, rhs)
            | ExprKind::Le(lhs, rhs)
            | ExprKind::Ge(lhs, rhs)
            | ExprKind::Gt(lhs, rhs)
            | ExprKind::And(lhs, rhs)
            | ExprKind::Or(lhs, rhs) => {
                self.optimize_expr(lhs);
                self.optimize_expr(rhs);
            }
            ExprKind::Call { args, .. } => {
                for arg in args {
                    self.optimize_expr(arg);
                }
            }
            ExprKind::Printf(specs) => {
                for spec in specs {
                    if let FormatSpec::Value(expr) = spec {
                        self.optimize_expr(expr);
                    }
                }
            }
            ExprKind::Tuple(fs) => {
                for value in fs {
                    self.optimize_expr(value);
                }
            }
            ExprKind::StructValue(fs) => {
                for (_, value) in fs {
                    self.optimize_expr(value);
                }
            }
            ExprKind::Int64(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::IndexAccess { .. }
            | ExprKind::FieldAccess { .. }
            | ExprKind::TmpVar(_)
            | ExprKind::Var(_) => {}
        }
    }
}

// Temporary variable used (refed) counting

fn inc_used<'a, 'tcx>(expr: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
    if let ExprKind::TmpVar(t) = expr.kind() {
        t.used.set(t.used.get() + 1);
    }

    expr
}

fn dcr_used_and_prunable(expr: &Expr<'_, '_>) -> bool {
    if let ExprKind::TmpVar(t) = expr.kind() {
        let u = t.used.get();
        if u > 0 {
            let u = u - 1;
            t.used.set(u);

            return u == 0 && t.immediate.get().is_none();
        }
    }
    false
}
