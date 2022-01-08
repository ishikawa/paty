use crate::syntax::PatternKind;
use crate::{sem, syntax};
use typed_arena::Arena;

#[derive(Debug)]
pub struct Program<'a> {
    pub functions: Vec<Function<'a>>,
}

#[derive(Debug)]
pub struct Function<'a> {
    pub name: String,
    pub args: Vec<String>,
    pub body: Vec<Stmt<'a>>,
    /// Whether this function is `main` or not.
    pub is_entry_point: bool,
}

#[derive(Debug)]
pub enum Stmt<'a> {
    TmpVarDef {
        index: usize,
        init: &'a Expr<'a>,
    },
    VarDef {
        name: String,
        init: &'a Expr<'a>,
    },
    Cond {
        /// The index of temporary variable which holds the result.
        ret: Option<usize>,
        branches: Vec<Branch<'a>>,
    },
    // "return" statement
    Ret(&'a Expr<'a>),
    // "Phi" function for a basic block. This statement must appear at the end of
    // each branch. It will be removed if the result location of a branch is None and
    // an expression has no side-effect.
    Phi(&'a Expr<'a>),
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
    Value(Value),
}

#[derive(Debug)]
pub enum Value {
    /// Native "int" type.
    Int(i32),
    Int64(i64),
    TmpVar(usize),
    Var(String),
}

pub struct Builder<'a> {
    /// An allocation arena for expressions.
    expr_arena: &'a Arena<Expr<'a>>,
    /// The current index of temporary variables. It starts from 0 and
    /// incremented by creating a new temporary variable. This index will
    /// be saved and reset to 0 when function enter, and restored when function exit.
    tmp_var_index: usize,
}

impl<'a> Builder<'a> {
    pub fn new(expr_arena: &'a Arena<Expr<'a>>) -> Self {
        Self {
            expr_arena,
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

    fn next_temp_var(&mut self) -> usize {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        t
    }

    fn push_expr(&mut self, expr: &'a Expr<'a>, stmts: &mut Vec<Stmt<'a>>) -> &'a Expr<'a> {
        let t = self.next_temp_var();
        let stmt = Stmt::TmpVarDef {
            index: t,
            init: expr,
        };
        stmts.push(stmt);

        self.expr_arena.alloc(Expr::Value(Value::TmpVar(t)))
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
                let expr = self.expr_arena.alloc(Expr::Minus(a));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Add(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self.expr_arena.alloc(Expr::Add(a, b));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Sub(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self.expr_arena.alloc(Expr::Sub(a, b));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Mul(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self.expr_arena.alloc(Expr::Mul(a, b));

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Div(a, b) => {
                let a = self._build(a, program, stmts);
                let b = self._build(b, program, stmts);
                let expr = self.expr_arena.alloc(Expr::Div(a, b));

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
                        .map(|a| self._build(a, program, stmts))
                        .collect(),
                };
                let expr = self.expr_arena.alloc(expr);

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Puts(args) => {
                let expr = Expr::Printf {
                    args: args
                        .iter()
                        .map(|a| self._build(a, program, stmts))
                        .collect(),
                };
                let expr = self.expr_arena.alloc(expr);

                self.push_expr(expr, stmts)
            }
            syntax::ExprKind::Let { name, rhs, then } => {
                let init = self._build(rhs, program, stmts);
                let stmt = Stmt::VarDef {
                    name: name.clone(),
                    init,
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
                body_stmts.push(Stmt::Ret(ret));

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
                                let lhs = self.expr_arena.alloc(Expr::Ge(t_head, lo));

                                let rhs = match end {
                                    syntax::RangeEnd::Included => {
                                        self.expr_arena.alloc(Expr::Le(t_head, hi))
                                    }
                                    syntax::RangeEnd::Excluded => {
                                        self.expr_arena.alloc(Expr::Lt(t_head, hi))
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
                        branch_stmts.push(Stmt::Phi(ret));

                        Branch {
                            condition: Some(condition),
                            body: branch_stmts,
                        }
                    })
                    .collect::<Vec<_>>();

                if let Some(else_body) = else_body {
                    let mut branch_stmts = vec![];
                    let ret = self._build(else_body, program, &mut branch_stmts);
                    branch_stmts.push(Stmt::Phi(ret));

                    let branch = Branch {
                        condition: None,
                        body: branch_stmts,
                    };
                    branches.push(branch);
                }

                let t = self.next_temp_var();
                let stmt = Stmt::Cond {
                    branches,
                    ret: Some(t),
                };
                stmts.push(stmt);

                self.expr_arena.alloc(Expr::Value(Value::TmpVar(t)))
            }
        }
    }
}
