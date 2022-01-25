use crate::syntax::PatternKind;
use crate::ty::{Type, TypeContext};
use crate::{sem, syntax};
use std::cell::Cell;
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
        if !self.decl_types.contains(&ty) {
            self.decl_types.push(ty);
        }
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

#[derive(Debug)]
pub struct Var<'tcx> {
    pub name: String,
    pub ty: &'tcx Type<'tcx>,
}

impl<'tcx> Var<'tcx> {
    pub fn new(name: String, ty: &'tcx Type<'tcx>) -> Self {
        Self { name, ty }
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
        self.ty
    }
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
        args: Vec<&'a Expr<'a, 'tcx>>,
    },

    // Built-in procedures
    Printf(Vec<FormatSpec<'a, 'tcx>>),

    // Values
    Int64(i64),
    Bool(bool),
    Str(String),
    Tuple(Vec<&'a Expr<'a, 'tcx>>),
    TupleField {
        operand: &'a Expr<'a, 'tcx>,
        index: usize,
    },
    TmpVar(&'a TmpVar<'a, 'tcx>),
    Var(&'tcx Type<'tcx>, String),
}

#[derive(Debug, Clone)]
pub enum FormatSpec<'a, 'tcx> {
    Value(&'a Expr<'a, 'tcx>),
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

impl<'a, 'pcx: 'tcx, 'tcx> Builder<'a, 'tcx> {
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

    pub fn build(&mut self, ast: &sem::SemAST<'pcx, 'tcx>) -> Program<'a, 'tcx> {
        let mut program = Program::new();
        let mut stmts = vec![];

        // Build top level statements and function definitions.
        self._build(ast.expr(), &mut program, &mut stmts);

        // Add `return 0` statement for the entry point function if needed.
        if !matches!(stmts.last(), Some(Stmt::Ret(_))) {
            stmts.push(Stmt::Ret(self.native_int(0)))
        }

        let main = Function {
            name: "main".to_string(),
            params: vec![],
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

    fn _build(
        &mut self,
        expr: &'pcx syntax::Expr<'pcx, 'tcx>,
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
                let tuple_ty = expr.expect_ty();
                program.add_decl_type(tuple_ty);

                let mut values = vec![];

                for sub in sub_exprs {
                    let value = self._build(sub, program, stmts);
                    values.push(inc_used(value));
                }

                let kind = ExprKind::Tuple(values);
                self.push_expr_kind(kind, tuple_ty, stmts)
            }
            syntax::ExprKind::Minus(a) => {
                let a = self._build(a, program, stmts);
                let kind = ExprKind::Minus(inc_used(a));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Add(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Add(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Sub(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Sub(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Mul(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Mul(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Div(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Div(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Eq(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Eq(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Ne(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Ne(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Lt(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Lt(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Gt(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Gt(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Le(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Le(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Ge(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Ge(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::And(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::And(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Or(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Or(inc_used(a), inc_used(b));

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Var(name) => {
                let kind = ExprKind::Var(expr.ty().unwrap(), name.clone());
                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::TupleField(operand, index) => {
                let operand = self._build(operand, program, stmts);
                let kind = ExprKind::TupleField {
                    operand: inc_used(operand),
                    index: *index,
                };

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Call(name, args) => {
                let kind = ExprKind::Call {
                    name: name.clone(),
                    args: args
                        .iter()
                        .map(|a| {
                            let a = self._build(a, program, stmts);
                            inc_used(a)
                        })
                        .collect(),
                };

                self.push_expr_kind(kind, expr.expect_ty(), stmts)
            }
            syntax::ExprKind::Puts(args) => {
                // Generates `printf(...)` code for `puts(...)`.
                let mut format_specs = vec![];

                // Build format specifiers
                let mut it = args.iter().peekable();

                while let Some(arg) = it.next() {
                    let a = self._build(arg, program, stmts);
                    self._printf_format(a, program, stmts, &mut format_specs);

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
            syntax::ExprKind::Let { pattern, rhs, then } => {
                let init = self._build(rhs, program, stmts);

                match pattern.kind() {
                    PatternKind::Variable(name) => {
                        let stmt = Stmt::VarDef {
                            name: name.clone(),
                            init: inc_used(init),
                        };
                        stmts.push(stmt);
                    }
                    PatternKind::Wildcard => {
                        // no bound variable to `_`
                    }
                    PatternKind::Integer(_)
                    | PatternKind::Boolean(_)
                    | PatternKind::String(_)
                    | PatternKind::Range { .. }
                    | PatternKind::Tuple(_) => {
                        unreachable!("Unsupported let pattern: `{}`", pattern.kind());
                    }
                }

                self._build(then, program, stmts)
            }
            syntax::ExprKind::Fn(syntax_fun) => {
                // save and reset temp var index
                let saved_tmp_var_index = self.tmp_var_index;
                self.tmp_var_index = 0;

                // convert parameter pattern to parameter name and assign variable.
                let mut params = vec![];

                for p in syntax_fun.params() {
                    let pat = p.pattern();
                    let param = match pat.kind() {
                        PatternKind::Variable(name) => Parameter::Var(Var {
                            name: name.to_string(),
                            ty: pat.expect_ty(),
                        }),
                        PatternKind::Wildcard => {
                            // ignore pattern but we have to define a parameter.
                            let t = self.next_temp_var(pat.expect_ty());
                            Parameter::TmpVar(t)
                        }
                        PatternKind::Integer(_)
                        | PatternKind::Boolean(_)
                        | PatternKind::String(_)
                        | PatternKind::Range { .. }
                        | PatternKind::Tuple(_) => {
                            unreachable!("Unsupported let pattern: `{}`", p.pattern().kind());
                        }
                    };

                    params.push(param);
                }

                let mut body_stmts = vec![];
                let ret = self._build(syntax_fun.body(), program, &mut body_stmts);
                body_stmts.push(Stmt::Ret(inc_used(ret)));

                let retty = syntax_fun.body().ty().unwrap();

                let fun = Function {
                    name: syntax_fun.name().to_string(),
                    params,
                    body: body_stmts,
                    retty,
                    is_entry_point: false,
                };
                program.functions.push(fun);

                // restore
                self.tmp_var_index = saved_tmp_var_index;
                self._build(syntax_fun.then(), program, stmts)
            }
            syntax::ExprKind::Case {
                head,
                arms,
                else_body,
            } => {
                let t = self.next_temp_var(expr.ty().unwrap());
                let t_head = self._build(head, program, stmts);

                // Construct "if-else" statement from each branches.
                let mut branches = arms
                    .iter()
                    .map(|arm| {
                        // Build an condition and variable declarations from the pattern
                        let mut branch_stmts = vec![];
                        let condition =
                            self._build_pattern(t_head, arm.pattern(), &mut branch_stmts);
                        let ret = self._build(arm.body(), program, &mut branch_stmts);

                        branch_stmts.push(Stmt::Phi {
                            var: t,
                            value: inc_used(ret),
                            pruned: Cell::new(false),
                        });

                        Branch {
                            condition: Some(condition),
                            body: branch_stmts,
                        }
                    })
                    .collect::<Vec<_>>();

                if let Some(else_body) = else_body {
                    let mut branch_stmts = vec![];
                    let ret = self._build(else_body, program, &mut branch_stmts);
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
    ) {
        match arg.ty() {
            Type::Int64 | Type::NativeInt | Type::Boolean | Type::String => {
                specs.push(FormatSpec::Value(inc_used(arg)));
            }
            Type::Tuple(fs) => {
                let mut it = fs.iter().enumerate().peekable();

                specs.push(FormatSpec::Str("("));
                while let Some((i, sub_ty)) = it.next() {
                    let kind = ExprKind::TupleField {
                        operand: inc_used(arg),
                        index: i,
                    };

                    let ir_expr = self.push_expr_kind(kind, sub_ty, stmts);
                    self._printf_format(ir_expr, program, stmts, specs);

                    if it.peek().is_some() {
                        specs.push(FormatSpec::Str(", "));
                    }
                }
                specs.push(FormatSpec::Str(")"));
            }
            Type::Undetermined => unreachable!("untyped code"),
        }
    }

    fn _build_pattern(
        &mut self,
        t_expr: &'a Expr<'a, 'tcx>,
        pat: &'pcx syntax::Pattern<'pcx, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        match pat.kind() {
            PatternKind::Integer(n) => {
                let value = self.int64(*n);
                let eq = ExprKind::Eq(inc_used(t_expr), value);

                self.expr_arena.alloc(Expr::new(eq, self.tcx.boolean()))
            }
            PatternKind::Boolean(b) => {
                if *b {
                    inc_used(t_expr)
                } else {
                    let expr = ExprKind::Not(inc_used(t_expr));
                    self.expr_arena.alloc(Expr::new(expr, self.tcx.boolean()))
                }
            }
            PatternKind::String(s) => {
                // Compare the value of head expression and pattern string with
                // POSIX `strcmp` function.
                let value = self.const_string(s);
                let kind = ExprKind::Call {
                    name: "strcmp".to_string(),
                    args: vec![inc_used(t_expr), value],
                };
                let strcmp = self.expr_arena.alloc(Expr::new(kind, self.tcx.int64()));

                let zero = self.native_int(0);
                let eq = ExprKind::Eq(inc_used(strcmp), zero);

                self.expr_arena.alloc(Expr::new(eq, self.tcx.boolean()))
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

                self.expr_arena.alloc(Expr::new(kind, self.tcx.boolean()))
            }
            PatternKind::Tuple(sub_pats) => {
                if sub_pats.is_empty() {
                    // Empty tuple is always matched with an empty tuple.
                    self.bool(true)
                } else {
                    let kind = ExprKind::TupleField {
                        operand: inc_used(t_expr),
                        index: 0,
                    };
                    let operand = self
                        .expr_arena
                        .alloc(Expr::new(kind, sub_pats[0].expect_ty()));

                    let mut condition = self._build_pattern(operand, sub_pats[0], stmts);

                    for (i, pat) in sub_pats.iter().enumerate().skip(1) {
                        let kind = ExprKind::TupleField {
                            operand: inc_used(t_expr),
                            index: i,
                        };
                        let operand = self.expr_arena.alloc(Expr::new(kind, pat.expect_ty()));

                        let kind =
                            ExprKind::And(condition, self._build_pattern(operand, pat, stmts));
                        condition = self.expr_arena.alloc(Expr::new(kind, self.tcx.boolean()))
                    }

                    condition
                }
            }
            PatternKind::Variable(name) => {
                stmts.push(Stmt::VarDef {
                    name: name.clone(),
                    init: inc_used(t_expr),
                });

                self.bool(true)
            }
            PatternKind::Wildcard => self.bool(true),
        }
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
                if var.used.get() == 1 {
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
            ExprKind::Int64(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::Tuple(_)
            | ExprKind::TupleField { .. }
            | ExprKind::TmpVar(_)
            | ExprKind::Var(_, _) => {}
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
