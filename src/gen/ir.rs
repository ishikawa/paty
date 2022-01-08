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
            if i == (self.args.len() - 1) {
                write!(f, ", ")?;
            }
        }
        writeln!(f, "):")?;
        for stmt in &self.body {
            let lines = stmt.to_string();
            let lines = lines.split("\n");
            for line in lines {
                writeln!(f, "  {}", line)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct TmpVar {
    pub index: usize,
    pub used: Cell<usize>,
}

impl TmpVar {
    pub fn new(index: usize) -> Self {
        Self {
            index,
            used: Cell::new(0),
        }
    }
}

#[derive(Debug)]
pub enum Stmt<'a> {
    TmpVarDef {
        var: &'a TmpVar,
        init: &'a Expr<'a>,
    },
    VarDef {
        name: String,
        init: &'a Expr<'a>,
    },
    Cond {
        /// The index of temporary variable which holds the result.
        ret: &'a TmpVar,
        branches: Vec<Branch<'a>>,
    },
    // "return" statement
    Ret(&'a Expr<'a>),
    // "Phi" function for a basic block. This statement must appear at the end of
    // each branch.
    Phi(&'a Expr<'a>),
}

impl fmt::Display for Stmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::TmpVarDef { var, init } => {
                write!(f, "t{} (used: {}) = {:?}", var.index, var.used.get(), init)?;
            }
            Stmt::VarDef { name, init } => {
                write!(f, "{} = {:?}", name, init)?;
            }
            Stmt::Ret(expr) => {
                write!(f, "return {:?}", expr)?;
            }
            Stmt::Phi(tmp) => {
                write!(f, "phi {:?}", tmp)?;
            }
            Stmt::Cond { ret, branches } => {
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
    Lt(&'a Expr<'a>, &'a Expr<'a>),
    Le(&'a Expr<'a>, &'a Expr<'a>),
    Gt(&'a Expr<'a>, &'a Expr<'a>),
    Ge(&'a Expr<'a>, &'a Expr<'a>),
    Eq(&'a Expr<'a>, &'a Expr<'a>),
    And(&'a Expr<'a>, &'a Expr<'a>),
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
    TmpVar(&'a TmpVar),
    Var(String),
}

pub struct Builder<'a> {
    /// An arena allocators for nodes.
    expr_arena: &'a Arena<Expr<'a>>,
    tmp_var_arena: &'a Arena<TmpVar>,
    /// The current index of temporary variables. It starts from 0 and
    /// incremented by creating a new temporary variable. This index will
    /// be saved and reset to 0 when function enter, and restored when function exit.
    tmp_var_index: usize,
}

impl<'a> Builder<'a> {
    pub fn new(expr_arena: &'a Arena<Expr<'a>>, tmp_var_arena: &'a Arena<TmpVar>) -> Self {
        Self {
            expr_arena,
            tmp_var_arena,
            tmp_var_index: 0,
        }
    }

    pub fn build(&mut self, ast: &sem::SemAST) -> Program {
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
        program
    }

    fn next_temp_var(&mut self) -> &'a TmpVar {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        self.tmp_var_arena.alloc(TmpVar::new(t))
    }

    fn push_expr(&mut self, expr: &'a Expr<'a>, stmts: &mut Vec<Stmt<'a>>) -> &'a Expr<'a> {
        let t = self.next_temp_var();
        let stmt = Stmt::TmpVarDef {
            var: t,
            init: self.mark_used(expr),
        };
        stmts.push(stmt);

        self.expr_arena.alloc(Expr::Value(Value::TmpVar(t)))
    }

    fn mark_used(&self, expr: &'a Expr<'a>) -> &'a Expr<'a> {
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
            syntax::ExprKind::Minus(a) => {
                let a = self._build(a, program, stmts);
                let expr = self.expr_arena.alloc(Expr::Minus(self.mark_used(a)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Add(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Add(self.mark_used(a), self.mark_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Sub(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Sub(self.mark_used(a), self.mark_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Mul(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Mul(self.mark_used(a), self.mark_used(b)));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Div(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self
                    .expr_arena
                    .alloc(Expr::Div(self.mark_used(a), self.mark_used(b)));

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
                            self.mark_used(a)
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
                            self.mark_used(a)
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
                    init: self.mark_used(init),
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
                body_stmts.push(Stmt::Ret(self.mark_used(ret)));

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
                let t_head = self._build(head, program, stmts);

                // Construct "if-else" statement from each branches.
                let mut branches = arms
                    .iter()
                    .map(|arm| {
                        // Build an immediate value from the pattern
                        let condition = match arm.pattern().kind() {
                            PatternKind::Integer(n) => {
                                let value = self.expr_arena.alloc(Expr::Value(Value::Int64(*n)));
                                let eq = Expr::Eq(t_head, value);

                                self.expr_arena.alloc(eq)
                            }
                            PatternKind::Range { lo, hi, end } => {
                                let lo = self.expr_arena.alloc(Expr::Value(Value::Int64(*lo)));
                                let hi = self.expr_arena.alloc(Expr::Value(Value::Int64(*hi)));
                                let lhs =
                                    self.expr_arena.alloc(Expr::Ge(self.mark_used(t_head), lo));

                                let rhs = match end {
                                    syntax::RangeEnd::Included => {
                                        self.expr_arena.alloc(Expr::Le(self.mark_used(t_head), hi))
                                    }
                                    syntax::RangeEnd::Excluded => {
                                        self.expr_arena.alloc(Expr::Lt(self.mark_used(t_head), hi))
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
                        branch_stmts.push(Stmt::Phi(self.mark_used(ret)));

                        Branch {
                            condition: Some(condition),
                            body: branch_stmts,
                        }
                    })
                    .collect::<Vec<_>>();

                if let Some(else_body) = else_body {
                    let mut branch_stmts = vec![];
                    let ret = self._build(else_body, program, &mut branch_stmts);
                    branch_stmts.push(Stmt::Phi(self.mark_used(ret)));

                    let branch = Branch {
                        condition: None,
                        body: branch_stmts,
                    };
                    branches.push(branch);
                }

                let t = self.next_temp_var();
                let stmt = Stmt::Cond { branches, ret: t };
                stmts.push(stmt);

                self.expr_arena.alloc(Expr::Value(Value::TmpVar(t)))
            }
        }
    }
}
