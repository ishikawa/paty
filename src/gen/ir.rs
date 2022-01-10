use crate::syntax::PatternKind;
use crate::typing::Type;
use crate::{sem, syntax};
use std::cell::Cell;
use std::fmt;
use typed_arena::Arena;

#[derive(Debug)]
pub struct Program<'a> {
    pub functions: Vec<Function<'a>>,
}

impl fmt::Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for fun in &self.functions {
            write!(f, "{}", fun)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Function<'a> {
    pub name: String,
    pub params: Vec<Parameter>,
    pub body: Vec<Stmt<'a>>,
    /// Whether this function is `main` or not.
    pub is_entry_point: bool,
}

impl fmt::Display for Function<'_> {
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
pub struct Parameter {
    pub name: String,
    pub ty: Type,
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        write!(f, ": ")?;
        write!(f, "{}", self.ty)?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct TmpVar<'a> {
    pub index: usize,
    pub ty: Type,
    pub used: Cell<usize>,
    pub immediate: Cell<Option<&'a Expr<'a>>>,
}

impl<'a> TmpVar<'a> {
    pub fn new(index: usize, ty: Type) -> Self {
        Self {
            index,
            ty,
            used: Cell::new(0),
            immediate: Cell::new(None),
        }
    }
}

#[derive(Debug)]
pub enum Stmt<'a> {
    TmpVarDef {
        var: &'a TmpVar<'a>,
        init: &'a Expr<'a>,
        pruned: Cell<bool>,
    },
    VarDef {
        name: String,
        init: &'a Expr<'a>,
    },
    Cond {
        /// The index of temporary variable which holds the result.
        var: &'a TmpVar<'a>,
        branches: Vec<Branch<'a>>,
    },
    // "Phi" function for a basic block. This statement must appear at the end of
    // each branch.
    Phi {
        var: &'a TmpVar<'a>,
        value: &'a Expr<'a>,
        pruned: Cell<bool>,
    },
    // "return" statement
    Ret(&'a Expr<'a>),
}

impl fmt::Display for Stmt<'_> {
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
pub struct Branch<'a> {
    pub condition: Option<&'a Expr<'a>>,
    pub body: Vec<Stmt<'a>>,
}

#[derive(Debug)]
pub struct Expr<'a> {
    kind: ExprKind<'a>,
    ty: Type,
}

impl<'a> Expr<'a> {
    pub fn new(kind: ExprKind<'a>, ty: Type) -> Self {
        Self { kind, ty }
    }

    pub fn int64(value: i64) -> Self {
        Self {
            kind: ExprKind::Value(Value::Int64(value)),
            ty: Type::Int64,
        }
    }

    pub fn bool(value: bool) -> Self {
        Self {
            kind: ExprKind::Value(Value::Bool(value)),
            ty: Type::Boolean,
        }
    }

    pub fn kind(&self) -> &ExprKind<'a> {
        &self.kind
    }

    pub fn ty(&self) -> Type {
        self.ty
    }
}

#[derive(Debug)]
pub enum ExprKind<'a> {
    Minus(&'a Expr<'a>),
    Not(&'a Expr<'a>),
    Add(&'a Expr<'a>, &'a Expr<'a>),
    Sub(&'a Expr<'a>, &'a Expr<'a>),
    Mul(&'a Expr<'a>, &'a Expr<'a>),
    Div(&'a Expr<'a>, &'a Expr<'a>),
    Eq(&'a Expr<'a>, &'a Expr<'a>),
    Ne(&'a Expr<'a>, &'a Expr<'a>),
    Lt(&'a Expr<'a>, &'a Expr<'a>),
    Le(&'a Expr<'a>, &'a Expr<'a>),
    Gt(&'a Expr<'a>, &'a Expr<'a>),
    Ge(&'a Expr<'a>, &'a Expr<'a>),
    And(&'a Expr<'a>, &'a Expr<'a>),
    Or(&'a Expr<'a>, &'a Expr<'a>),
    Call {
        name: String,
        args: Vec<&'a Expr<'a>>,
    },
    Printf {
        args: Vec<&'a Expr<'a>>,
    },
    Value(Value<'a>),
}

#[derive(Debug)]
pub enum Value<'a> {
    /// Native "int" type.
    Int(i32),
    Int64(i64),
    Bool(bool),
    TmpVar(&'a TmpVar<'a>),
    Var(String, Type),
}

pub struct Builder<'a> {
    /// An arena allocators for nodes.
    expr_arena: &'a Arena<Expr<'a>>,
    tmp_var_arena: &'a Arena<TmpVar<'a>>,
    /// The current index of temporary variables. It starts from 0 and
    /// incremented by creating a new temporary variable. This index will
    /// be saved and reset to 0 when function enter, and restored when function exit.
    tmp_var_index: usize,
}

impl<'a> Builder<'a> {
    pub fn new(expr_arena: &'a Arena<Expr<'a>>, tmp_var_arena: &'a Arena<TmpVar<'a>>) -> Self {
        Self {
            expr_arena,
            tmp_var_arena,
            tmp_var_index: 0,
        }
    }

    pub fn build(&mut self, ast: &sem::SemAST) -> Program<'a> {
        let mut program = Program { functions: vec![] };
        let mut stmts = vec![];

        // Build top level statements and function definitions.
        self._build(ast.expr(), &mut program, &mut stmts);
        // Add `return 0` statement for the entry point function if needed.
        if !matches!(stmts.last(), Some(Stmt::Ret(_))) {
            let kind = ExprKind::Value(Value::Int(0));
            let expr = Expr::new(kind, Type::Int64);
            let expr = self.expr_arena.alloc(expr);

            stmts.push(Stmt::Ret(expr))
        }

        let main = Function {
            name: "main".to_string(),
            params: vec![],
            body: stmts,
            is_entry_point: true,
        };
        program.functions.push(main);

        // post process
        let mut optimizer = Optimizer::new();
        optimizer.optimize(&mut program);

        program
    }

    fn next_temp_var(&mut self, ty: Type) -> &'a TmpVar<'a> {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        self.tmp_var_arena.alloc(TmpVar::new(t, ty))
    }

    fn push_expr(
        &mut self,
        kind: ExprKind<'a>,
        syntax_expr: &syntax::Expr,
        stmts: &mut Vec<Stmt<'a>>,
    ) -> &'a Expr<'a> {
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

    fn inc_used(&self, expr: &'a Expr<'a>) -> &'a Expr<'a> {
        if let ExprKind::Value(Value::TmpVar(t)) = expr.kind() {
            t.used.set(t.used.get() + 1);
        }

        expr
    }

    fn _build(
        &mut self,
        expr: &syntax::Expr,
        program: &mut Program<'a>,
        stmts: &mut Vec<Stmt<'a>>,
    ) -> &'a Expr<'a> {
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
                                let value = self.expr_arena.alloc(Expr::int64(*n));
                                let eq = ExprKind::Eq(self.inc_used(t_head), value);

                                self.expr_arena.alloc(Expr::new(eq, Type::Boolean))
                            }
                            PatternKind::Boolean(b) => {
                                if *b {
                                    self.inc_used(t_head)
                                } else {
                                    let expr = ExprKind::Not(self.inc_used(t_head));
                                    self.expr_arena.alloc(Expr::new(expr, Type::Boolean))
                                }
                            }
                            PatternKind::Range { lo, hi, end } => {
                                let lo = self.expr_arena.alloc(Expr::int64(*lo));
                                let hi = self.expr_arena.alloc(Expr::int64(*hi));

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
                                    self.expr_arena.alloc(Expr::new(lhs, Type::Boolean)),
                                    self.expr_arena.alloc(Expr::new(rhs, Type::Boolean)),
                                );

                                self.expr_arena.alloc(Expr::new(kind, Type::Boolean))
                            }
                            PatternKind::Wildcard => self.expr_arena.alloc(Expr::bool(true)),
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

impl<'a> Optimizer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn optimize(&mut self, program: &mut Program<'a>) {
        for fun in &mut program.functions {
            self.optimize_function(fun);
        }
    }

    fn decr_used_and_prunable(&self, expr: &'a Expr<'a>) -> bool {
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

    fn optimize_function(&mut self, fun: &Function<'a>) {
        for stmt in &fun.body {
            self.optimize_stmt(stmt);
        }
    }

    fn optimize_stmt(&mut self, stmt: &Stmt<'a>) {
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

    fn optimize_expr(&mut self, expr: &Expr<'a>) {
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
