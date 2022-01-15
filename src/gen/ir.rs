use crate::syntax::PatternKind;
use crate::ty::{Type, TypeContext};
use crate::{sem, syntax};
use std::cell::Cell;
use std::fmt;
use typed_arena::Arena;

#[derive(Debug)]
pub struct Program<'a, 'tcx> {
    pub functions: Vec<Function<'a, 'tcx>>,
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
    pub params: Vec<Parameter<'tcx>>,
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
pub struct Parameter<'tcx> {
    pub name: String,
    pub ty: &'tcx Type<'tcx>,
}

impl fmt::Display for Parameter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        write!(f, ": ")?;
        write!(f, "{}", self.ty)?;
        Ok(())
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
    Printf {
        args: Vec<&'a Expr<'a, 'tcx>>,
    },
    Value(Value<'a, 'tcx>),
}

#[derive(Debug)]
pub enum Value<'a, 'tcx> {
    /// Native "int" type.
    Int(i32),
    Int64(i64),
    Bool(bool),
    String(String),
    TmpVar(&'a TmpVar<'a, 'tcx>),
    Var(String, &'tcx Type<'tcx>),
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
        let mut program = Program { functions: vec![] };
        let mut stmts = vec![];

        // Build top level statements and function definitions.
        self._build(ast.expr(), &mut program, &mut stmts);

        // Add `return 0` statement for the entry point function if needed.
        let c_int_ty = self.tcx.native_int();
        if !matches!(stmts.last(), Some(Stmt::Ret(_))) {
            let kind = ExprKind::Value(Value::Int(0));
            let expr = Expr::new(kind, c_int_ty);
            let expr = self.expr_arena.alloc(expr);

            stmts.push(Stmt::Ret(expr))
        }

        let main = Function {
            name: "main".to_string(),
            params: vec![],
            body: stmts,
            retty: c_int_ty,
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
        kind: ExprKind<'a, 'tcx>,
        syntax_expr: &syntax::Expr<'pcx, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let expr_ty = syntax_expr.ty().unwrap_or_else(|| {
            panic!(
                "Semantic analyzer can't assign type for expression {:?}",
                syntax_expr
            );
        });

        let expr = self.expr_arena.alloc(Expr::new(kind, expr_ty));
        let t = self.next_temp_var(expr.ty());
        let stmt = Stmt::TmpVarDef {
            var: t,
            init: expr,
            pruned: Cell::new(false),
        };
        stmts.push(stmt);

        let kind = ExprKind::Value(Value::TmpVar(t));
        self.expr_arena.alloc(Expr::new(kind, expr.ty()))
    }

    fn inc_used(&self, expr: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        if let ExprKind::Value(Value::TmpVar(t)) = expr.kind() {
            t.used.set(t.used.get() + 1);
        }

        expr
    }

    fn int64(&self, value: i64) -> Expr<'a, 'tcx> {
        let kind = ExprKind::Value(Value::Int64(value));
        let ty = self.tcx.int64();

        Expr::new(kind, ty)
    }

    fn native_int(&self, value: i32) -> Expr<'a, 'tcx> {
        let kind = ExprKind::Value(Value::Int(value));
        let ty = self.tcx.native_int();

        Expr::new(kind, ty)
    }

    fn bool(&self, value: bool) -> Expr<'a, 'tcx> {
        let kind = ExprKind::Value(Value::Bool(value));
        let ty = self.tcx.boolean();

        Expr::new(kind, ty)
    }

    fn const_string(&self, value: &str) -> Expr<'a, 'tcx> {
        let kind = ExprKind::Value(Value::String(value.to_string()));
        let ty = self.tcx.string();

        Expr::new(kind, ty)
    }

    fn _build(
        &mut self,
        expr: &'pcx syntax::Expr<'pcx, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        match expr.kind() {
            syntax::ExprKind::Integer(n) => {
                let value = Value::Int64(*n);
                let kind = ExprKind::Value(value);

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Boolean(b) => {
                let value = Value::Bool(*b);
                let kind = ExprKind::Value(value);

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::String(s) => {
                let value = Value::String(s.to_string());
                let kind = ExprKind::Value(value);

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Minus(a) => {
                let a = self._build(a, program, stmts);
                let kind = ExprKind::Minus(self.inc_used(a));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Add(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Add(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Sub(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Sub(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Mul(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Mul(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Div(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Div(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Eq(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Eq(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Ne(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Ne(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Lt(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Lt(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Gt(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Gt(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Le(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Le(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Ge(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Ge(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::And(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::And(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Or(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let kind = ExprKind::Or(self.inc_used(a), self.inc_used(b));

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Var(name) => {
                let value = Value::Var(name.clone(), expr.ty().unwrap());
                let kind = ExprKind::Value(value);

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Call(name, args) => {
                let kind = ExprKind::Call {
                    name: name.clone(),
                    args: args
                        .iter()
                        .map(|a| {
                            let a = self._build(a, program, stmts);
                            self.inc_used(a)
                        })
                        .collect(),
                };

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Puts(args) => {
                let kind = ExprKind::Printf {
                    args: args
                        .iter()
                        .map(|a| {
                            let a = self._build(a, program, stmts);
                            self.inc_used(a)
                        })
                        .collect(),
                };

                self.push_expr(kind, expr, stmts)
            }
            syntax::ExprKind::Let { name, rhs, then } => {
                let init = self._build(rhs, program, stmts);
                let stmt = Stmt::VarDef {
                    name: name.clone(),
                    init: self.inc_used(init),
                };
                stmts.push(stmt);
                self._build(then, program, stmts)
            }
            syntax::ExprKind::Fn(syntax_fun) => {
                // save and reset temp var index
                let saved_tmp_var_index = self.tmp_var_index;
                self.tmp_var_index = 0;

                let mut body_stmts = vec![];
                let ret = self._build(syntax_fun.body(), program, &mut body_stmts);
                body_stmts.push(Stmt::Ret(self.inc_used(ret)));

                let retty = syntax_fun.body().ty().unwrap();

                let params = syntax_fun
                    .params()
                    .iter()
                    .map(|p| Parameter {
                        name: p.name().to_string(),
                        ty: p.ty(),
                    })
                    .collect();

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
                        // Build an immediate value from the pattern
                        let condition = match arm.pattern().kind() {
                            PatternKind::Integer(n) => {
                                let value = self.expr_arena.alloc(self.int64(*n));
                                let eq = ExprKind::Eq(self.inc_used(t_head), value);

                                self.expr_arena.alloc(Expr::new(eq, self.tcx.boolean()))
                            }
                            PatternKind::Boolean(b) => {
                                if *b {
                                    self.inc_used(t_head)
                                } else {
                                    let expr = ExprKind::Not(self.inc_used(t_head));
                                    self.expr_arena.alloc(Expr::new(expr, self.tcx.boolean()))
                                }
                            }
                            PatternKind::String(s) => {
                                // Compare the value of head expression and pattern string with
                                // POSIX `strcmp` function.
                                let value = self.expr_arena.alloc(self.const_string(s));
                                let kind = ExprKind::Call {
                                    name: "strcmp".to_string(),
                                    args: vec![self.inc_used(t_head), value],
                                };
                                let strcmp =
                                    self.expr_arena.alloc(Expr::new(kind, self.tcx.int64()));

                                let zero = self.expr_arena.alloc(self.native_int(0));
                                let eq = ExprKind::Eq(self.inc_used(strcmp), zero);

                                self.expr_arena.alloc(Expr::new(eq, self.tcx.boolean()))
                            }
                            PatternKind::Range { lo, hi, end } => {
                                let lo = self.expr_arena.alloc(self.int64(*lo));
                                let hi = self.expr_arena.alloc(self.int64(*hi));

                                let lhs = ExprKind::Ge(self.inc_used(t_head), lo);

                                let rhs = match end {
                                    syntax::RangeEnd::Included => {
                                        ExprKind::Le(self.inc_used(t_head), hi)
                                    }
                                    syntax::RangeEnd::Excluded => {
                                        ExprKind::Lt(self.inc_used(t_head), hi)
                                    }
                                };

                                let kind = ExprKind::And(
                                    self.expr_arena.alloc(Expr::new(lhs, self.tcx.boolean())),
                                    self.expr_arena.alloc(Expr::new(rhs, self.tcx.boolean())),
                                );

                                self.expr_arena.alloc(Expr::new(kind, self.tcx.boolean()))
                            }
                            PatternKind::Or(_, _) => todo!(),
                            PatternKind::Wildcard(_) => self.expr_arena.alloc(self.bool(true)),
                        };

                        let mut branch_stmts = vec![];
                        let ret = self._build(arm.body(), program, &mut branch_stmts);
                        branch_stmts.push(Stmt::Phi {
                            var: t,
                            value: self.inc_used(ret),
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
                        value: self.inc_used(ret),
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

                let kind = ExprKind::Value(Value::TmpVar(t));
                self.expr_arena.alloc(Expr::new(kind, t.ty))
            }
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

    fn decr_used_and_prunable(&self, expr: &'a Expr<'a, 'tcx>) -> bool {
        if let ExprKind::Value(Value::TmpVar(t)) = expr.kind() {
            let u = t.used.get();
            if u > 0 {
                let u = u - 1;
                t.used.set(u);

                return u == 0 && t.immediate.get().is_none();
            }
        }
        false
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
                    // replaced with the expression if it has no side-effect.
                    //if let Expr::Value(_) = init {
                    var.immediate.set(Some(init));
                    pruned.set(true);
                    return;
                    //}
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
                    if self.decr_used_and_prunable(value) {
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
            ExprKind::Printf { args } => {
                for arg in args {
                    self.optimize_expr(arg);
                }
            }
            ExprKind::Value(value) => self.optimize_value(value),
        }
    }

    fn optimize_value(&mut self, _value: &Value) {}
}
