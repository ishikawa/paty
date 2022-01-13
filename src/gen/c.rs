//! C code generator
use crate::ty::Type;

use super::ir::{Expr, ExprKind, Function, Program, Stmt, Value};

#[derive(Debug)]
pub struct Emitter {}

impl Default for Emitter {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, 'tcx> Emitter {
    pub fn new() -> Self {
        Self {}
    }

    pub fn emit(&mut self, program: &'a Program<'a, 'tcx>) -> String {
        let mut code = [
            "#include <stdio.h>",
            "#include <stdint.h>",
            "#include <stdbool.h>",
            "#include <inttypes.h>",
            "#include <string.h>",
            "\n",
        ]
        .join("\n");

        for fun in &program.functions {
            self.emit_function(fun, &mut code);
            code.push('\n');
        }

        code
    }

    fn emit_function(&mut self, fun: &Function<'a, 'tcx>, code: &mut String) {
        if fun.is_entry_point {
            // 'main' must return 'int'
            code.push_str(c_type(&Type::NativeInt));
        } else {
            code.push_str(c_type(fun.retty));
        }
        code.push(' ');

        code.push_str(&fun.name);
        code.push('(');
        for (i, param) in fun.params.iter().enumerate() {
            code.push_str(c_type(param.ty));
            code.push(' ');
            code.push_str(&param.name);

            if i != (fun.params.len() - 1) {
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

    fn emit_stmt(&mut self, stmt: &Stmt<'a, 'tcx>, code: &mut String) {
        match stmt {
            Stmt::TmpVarDef { var, init, pruned } => {
                if !pruned.get() {
                    if var.used.get() > 0 {
                        code.push_str(c_type(init.ty()));
                        code.push(' ');
                        code.push_str(&format!("t{} = ", var.index));
                    }
                    self.emit_expr(init, code);
                    code.push_str(";\n");
                }
            }
            Stmt::VarDef { name, init } => {
                code.push_str(c_type(init.ty()));
                code.push(' ');
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
            Stmt::Phi { var, value, pruned } => {
                if !pruned.get() {
                    if var.used.get() > 0 {
                        code.push_str(&format!("t{} = ", var.index));
                    }
                    self.emit_expr(value, code);
                    code.push_str(";\n");
                }
            }
            Stmt::Cond { branches, var } => {
                if var.used.get() > 0 {
                    code.push_str(c_type(var.ty));
                    code.push(' ');
                    code.push_str(&format!("t{}", var.index));
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
            }
        }
    }

    fn emit_expr(&mut self, expr: &Expr<'a, 'tcx>, code: &mut String) {
        match expr.kind() {
            ExprKind::Minus(operand) => {
                code.push('-');
                self.emit_expr(operand, code);
            }
            ExprKind::Not(operand) => {
                code.push('!');
                self.emit_expr(operand, code);
            }
            ExprKind::Add(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" + ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Sub(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" - ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Mul(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" * ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Div(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" / ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Lt(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" < ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Le(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" <= ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Gt(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" > ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Ge(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" >= ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Eq(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" == ");
                self.emit_expr(rhs, code);
            }
            ExprKind::Ne(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" != ");
                self.emit_expr(rhs, code);
            }
            ExprKind::And(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" && ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Or(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" || ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Call { name, args } => {
                code.push_str(&format!("{}(", name));
                for (i, arg) in args.iter().enumerate() {
                    self.emit_expr(arg, code);

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            ExprKind::Printf { args } => {
                code.push_str("printf(\"");
                for (i, arg) in args.iter().enumerate() {
                    match immediate(arg).ty() {
                        Type::Int64 => {
                            // Use standard conversion specifier macros for integer types.
                            code.push_str("%\" PRId64 \"");
                        }
                        Type::Boolean => {
                            // "true" / "false"
                            code.push_str("%s");
                        }
                        Type::String => {
                            code.push_str("%s");
                        }
                        Type::Tuple(_) => todo!(),
                        Type::NativeInt => {
                            code.push_str("%d");
                        }
                    }

                    // separated by a space
                    if i != (args.len() - 1) {
                        code.push(' ');
                    }
                }
                code.push_str("\\n\", ");

                for (i, arg) in args.iter().enumerate() {
                    match immediate(arg).ty() {
                        Type::Int64 | Type::String | Type::NativeInt => {
                            self.emit_expr(arg, code);
                        }
                        Type::Boolean => {
                            // "true" / "false"
                            code.push('(');
                            self.emit_expr(arg, code);
                            code.push_str(" ? \"true\" : \"false\"");
                            code.push(')');
                        }
                        Type::Tuple(_) => todo!(),
                    }

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            ExprKind::Value(value) => self.emit_value(value, code),
        }
    }

    fn emit_value(&mut self, value: &Value, code: &mut String) {
        match value {
            Value::Int(n) => code.push_str(&format!("{}", *n)),
            Value::Int64(n) => {
                // Use standard macros for integer constant expression to expand
                // a value to the type int_least_N.
                code.push_str(&format!("INT64_C({})", *n))
            }
            Value::Bool(b) => {
                // Use standard macros for boolean constant expression.
                if *b {
                    code.push_str("true");
                } else {
                    code.push_str("false");
                }
            }
            Value::String(s) => {
                code.push_str("u8\"");
                for c in s.escape_default() {
                    code.push(c);
                }
                code.push('"');
            }
            Value::TmpVar(t) => {
                if let Some(expr) = t.immediate.get() {
                    self.emit_expr(expr, code);
                } else {
                    code.push_str(&format!("t{}", t.index));
                }
            }
            Value::Var(name, _) => code.push_str(name),
        }
    }
}

fn immediate<'a, 'tcx>(expr: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
    if let ExprKind::Value(Value::TmpVar(t)) = expr.kind() {
        if let Some(expr) = t.immediate.get() {
            return expr;
        }
    }
    expr
}

fn c_type(ty: &Type) -> &'static str {
    match ty {
        Type::Int64 => "int64_t",
        Type::Boolean => "bool",
        Type::String => "const char *",
        Type::NativeInt => "int",
        Type::Tuple(_) => todo!(),
    }
}
