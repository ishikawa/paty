use crate::syntax::PatternKind;
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
    pub args: Vec<String>,
    pub body: Vec<Stmt<'a>>,
    /// Whether this function is `main` or not.
    pub is_entry_point: bool,
}

impl fmt::Display for Function<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        write!(f, "(")?;
        for (i, arg) in self.args.iter().enumerate() {
            write!(f, "{}", arg)?;
            if i < (self.args.len() - 1) {
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
pub struct TmpVar<'a> {
    pub index: usize,
    pub used: Cell<usize>,
    pub immediate: Cell<Option<&'a Expr<'a>>>,
}

impl<'a> TmpVar<'a> {
    pub fn new(index: usize) -> Self {
        Self {
            index,
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
pub enum Expr<'a> {
    Minus(&'a Expr<'a>),
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
    Var(String),
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
            let expr = Expr::Value(Value::Int(0));
            let expr = self.expr_arena.alloc(expr);

            stmts.push(Stmt::Ret(expr))
        }

        let main = Function {
            name: "main".to_string(),
            args: vec![],
            body: stmts,
            is_entry_point: true,
        };
        program.functions.push(main);

        // post process
        let mut optimizer = Optimizer::new();
        optimizer.optimize(&mut program);

        program
    }

    fn next_temp_var(&mut self) -> &'a TmpVar<'a> {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        self.tmp_var_arena.alloc(TmpVar::new(t))
    }

    fn push_expr(&mut self, expr: &'a Expr<'a>, stmts: &mut Vec<Stmt<'a>>) -> &'a Expr<'a> {
        let t = self.next_temp_var();
        let stmt = Stmt::TmpVarDef {
            var: t,
            init: expr,
            pruned: Cell::new(false),
        };
        stmts.push(stmt);

        self.expr_arena.alloc(Expr::Value(Value::TmpVar(t)))
    }

    fn inc_used(&self, expr: &'a Expr<'a>) -> &'a Expr<'a> {
        if let Expr::Value(Value::TmpVar(t)) = expr {
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
                let expr = self.expr_arena.alloc(Expr::Value(value));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Boolean(b) => {
                let value = Value::Bool(*b);
                let expr = self.expr_arena.alloc(Expr::Value(value));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Minus(a) => {
                let a = self._build(a, program, stmts);
                let expr = self.expr_arena.alloc(Expr::Minus(self.inc_used(a)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Add(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Add(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Sub(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Sub(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Mul(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Mul(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Div(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Div(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Eq(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Eq(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Ne(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Ne(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Lt(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Lt(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Gt(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Gt(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Le(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Le(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Ge(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Ge(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::And(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::And(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Or(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Or(self.inc_used(a), self.inc_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Var(name) => {
                let value = Value::Var(name.clone());
                let expr = self.expr_arena.alloc(Expr::Value(value));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Call(name, args) => {
                let expr = Expr::Call {
                    name: name.clone(),
                    args: args
                        .iter()
                        .map(|a| {
                            let a = self._build(a, program, stmts);
                            self.inc_used(a)
                        })
                        .collect(),
                };
                let expr = self.expr_arena.alloc(expr);

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Puts(args) => {
                let expr = Expr::Printf {
                    args: args
                        .iter()
                        .map(|a| {
                            let a = self._build(a, program, stmts);
                            self.inc_used(a)
                        })
                        .collect(),
                };
                let expr = self.expr_arena.alloc(expr);

                self.push_expr(expr, stmts)
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
            syntax::ExprKind::Fn {
                name,
                args,
                body,
                then,
            } => {
                // save and reset temp var index
                let saved_tmp_var_index = self.tmp_var_index;
                self.tmp_var_index = 0;

                let mut body_stmts = vec![];
                let ret = self._build(body, program, &mut body_stmts);
                body_stmts.push(Stmt::Ret(self.inc_used(ret)));

                let fun = Function {
                    name: name.clone(),
                    args: args.clone(),
                    body: body_stmts,
                    is_entry_point: false,
                };
                program.functions.push(fun);

                // restore
                self.tmp_var_index = saved_tmp_var_index;
                self._build(then, program, stmts)
            }
            syntax::ExprKind::Case {
                head,
                arms,
                else_body,
            } => {
                let t = self.next_temp_var();
                let t_head = self._build(head, program, stmts);

                // Construct "if-else" statement from each branches.
                let mut branches = arms
                    .iter()
                    .map(|arm| {
                        // Build an immediate value from the pattern
                        let condition = match arm.pattern().kind() {
                            PatternKind::Integer(n) => {
                                let value = self.expr_arena.alloc(Expr::Value(Value::Int64(*n)));
                                let eq = Expr::Eq(self.inc_used(t_head), value);

                                self.expr_arena.alloc(eq)
                            }
                            PatternKind::Boolean(b) => {
                                let value = self.expr_arena.alloc(Expr::Value(Value::Bool(*b)));
                                let eq = Expr::Eq(self.inc_used(t_head), value);

                                self.expr_arena.alloc(eq)
                            }
                            PatternKind::Range { lo, hi, end } => {
                                let lo = self.expr_arena.alloc(Expr::Value(Value::Int64(*lo)));
                                let hi = self.expr_arena.alloc(Expr::Value(Value::Int64(*hi)));
                                let lhs =
                                    self.expr_arena.alloc(Expr::Ge(self.inc_used(t_head), lo));

                                let rhs = match end {
                                    syntax::RangeEnd::Included => {
                                        self.expr_arena.alloc(Expr::Le(self.inc_used(t_head), hi))
                                    }
                                    syntax::RangeEnd::Excluded => {
                                        self.expr_arena.alloc(Expr::Lt(self.inc_used(t_head), hi))
                                    }
                                };
                                self.expr_arena.alloc(Expr::And(lhs, rhs))
                            }
                            PatternKind::Wildcard => {
                                self.expr_arena.alloc(Expr::Value(Value::Int64(1)))
                            }
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

                self.expr_arena.alloc(Expr::Value(Value::TmpVar(t)))
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
        if let Expr::Value(Value::TmpVar(t)) = expr {
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
        match expr {
            Expr::Minus(operand) => {
                self.optimize_expr(operand);
            }
            Expr::Add(lhs, rhs)
            | Expr::Sub(lhs, rhs)
            | Expr::Mul(lhs, rhs)
            | Expr::Div(lhs, rhs)
            | Expr::Eq(lhs, rhs)
            | Expr::Ne(lhs, rhs)
            | Expr::Lt(lhs, rhs)
            | Expr::Le(lhs, rhs)
            | Expr::Ge(lhs, rhs)
            | Expr::Gt(lhs, rhs)
            | Expr::And(lhs, rhs)
            | Expr::Or(lhs, rhs) => {
                self.optimize_expr(lhs);
                self.optimize_expr(rhs);
            }
            Expr::Call { args, .. } => {
                for arg in args {
                    self.optimize_expr(arg);
                }
            }
            Expr::Printf { args } => {
                for arg in args {
                    self.optimize_expr(arg);
                }
            }
            Expr::Value(value) => self.optimize_value(value),
        }
    }

    fn optimize_value(&mut self, _value: &Value) {}
}
