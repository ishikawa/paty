//! C code generator
use super::ir::{Expr, Function, Program, Stmt, TmpVar, Value};

#[derive(Debug)]
pub struct Emitter<'a> {
    phi_target: Option<&'a TmpVar>,
}

impl<'a> Default for Emitter<'a> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> Emitter<'a> {
    pub fn new() -> Self {
        Self { phi_target: None }
    }

    pub fn emit(&mut self, program: &'a Program<'a>) -> String {
        let mut code = [
            "#include <stdio.h>",
            "#include <stdint.h>",
            "#include <inttypes.h>",
            "",
        ]
        .join("\n");

        for fun in &program.functions {
            self.emit_function(fun, &mut code);
        }

        code
    }

    fn emit_function(&mut self, fun: &Function<'a>, code: &mut String) {
        if fun.is_entry_point {
            // 'main' must return 'int'
            code.push_str("int ");
        } else {
            code.push_str("int64_t ");
        }

        code.push_str(&fun.name);
        code.push('(');
        for (i, arg) in fun.args.iter().enumerate() {
            code.push_str("int64_t ");
            code.push_str(arg);

            if i != (fun.args.len() - 1) {
                code.push_str(", ");
            }
        }
        code.push_str(")\n");

        // body
        code.push_str("{\n");
        for stmt in &fun.body {
            self.emit_stmt(stmt, code);
        }
        code.push_str("}\n");
    }

    fn emit_stmt(&mut self, stmt: &Stmt<'a>, code: &mut String) {
        match stmt {
            Stmt::TmpVarDef { var, init } => {
                if var.used.get() > 0 {
                    code.push_str("int64_t ");
                    code.push_str(&format!("t{} = ", var.index));
                }
                self.emit_expr(init, code);
                code.push_str(";\n");
            }
            Stmt::VarDef { name, init } => {
                code.push_str("int64_t ");
                code.push_str(name);
                code.push_str(" = ");
                self.emit_expr(init, code);
                code.push_str(";\n");
            }
            Stmt::Ret(expr) => {
                code.push_str("return ");
                self.emit_expr(expr, code);
                code.push_str(";\n");
            }
            Stmt::Phi(expr) => {
                if let Some(var) = self.phi_target {
                    if var.used.get() > 0 {
                        code.push_str(&format!("t{} = ", var.index));
                    }
                }
                self.emit_expr(expr, code);
                code.push_str(";\n");
            }
            Stmt::Cond { branches, ret } => {
                let saved_phi_target = self.phi_target;
                self.phi_target = Some(ret);

                if ret.used.get() > 0 {
                    code.push_str("int64_t ");
                    code.push_str(&format!("t{}", ret.index));
                    code.push_str(";\n");
                }

                // Construct "if-else" statement from each branches.
                for (i, branch) in branches.iter().enumerate() {
                    if i > 0 {
                        code.push_str("else ");
                    }

                    if let Some(condition) = branch.condition {
                        code.push_str("if (");
                        self.emit_expr(condition, code);
                        code.push_str(") ");
                    }

                    // body
                    code.push_str("{\n");
                    for stmt in &branch.body {
                        self.emit_stmt(stmt, code);
                    }
                    code.push_str("}\n");
                }

                self.phi_target = saved_phi_target;
            }
        }
    }

    fn emit_expr(&mut self, expr: &Expr<'a>, code: &mut String) {
        match expr {
            Expr::Minus(operand) => {
                code.push('-');
                self.emit_expr(operand, code);
            }
            Expr::Add(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" + ");
                self.emit_expr(rhs, code);
            }
            Expr::Sub(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" - ");
                self.emit_expr(rhs, code);
            }
            Expr::Mul(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" * ");
                self.emit_expr(rhs, code);
            }
            Expr::Div(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" / ");
                self.emit_expr(rhs, code);
            }
            Expr::Lt(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" < ");
                self.emit_expr(rhs, code);
            }
            Expr::Le(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" <= ");
                self.emit_expr(rhs, code);
            }
            Expr::Gt(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" > ");
                self.emit_expr(rhs, code);
            }
            Expr::Ge(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" >= ");
                self.emit_expr(rhs, code);
            }
            Expr::Eq(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" == ");
                self.emit_expr(rhs, code);
            }
            Expr::And(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" && ");
                self.emit_expr(rhs, code);
            }
            Expr::Call { name, args } => {
                code.push_str(&format!("{}(", name));
                for (i, arg) in args.iter().enumerate() {
                    self.emit_expr(arg, code);

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            Expr::Printf { args } => {
                code.push_str("printf(\"");
                for (i, _) in args.iter().enumerate() {
                    // Use standard conversion specifier macros for integer types.
                    code.push_str("%\" PRId64 \"");

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push_str("\\n\", ");

                for (i, arg) in args.iter().enumerate() {
                    self.emit_expr(arg, code);

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            Expr::Value(value) => self.emit_value(value, code),
        }
    }

    fn emit_value(&mut self, value: &Value, code: &mut String) {
        match value {
            Value::Int(n) => code.push_str(&format!("{}", *n)),
            Value::Int64(n) =>
            // Use standard macros for integer constant expression to expand
            // a value to the type int_least_N.
            {
                code.push_str(&format!("INT64_C({})", *n))
            }
            Value::TmpVar(t) => code.push_str(&format!("t{}", t.index)),
            Value::Var(name) => code.push_str(name),
        }
    }
}
