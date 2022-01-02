//! C code generator
use crate::sem;
use crate::syntax;

#[derive(Debug)]
struct Emitter {
    main: String,
    functions: String,
    in_top_level: bool,
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            main: String::default(),
            functions: String::default(),
            in_top_level: true,
        }
    }

    pub fn emit(&self) -> String {
        [
            "#include <stdio.h>\n",
            "#include <stdint.h>\n",
            "#include <inttypes.h>\n",
            "\n",
            &self.functions,
            "\n",
            "int main(void)\n",
            "{\n",
            "  ",
            &self.main,
            "  return 0;\n",
            "}",
        ]
        .join("")
    }

    fn push_str<S: AsRef<str>>(&mut self, code: S) {
        if self.in_top_level {
            self.main.push_str(code.as_ref());
        } else {
            self.functions.push_str(code.as_ref());
        }
    }

    pub fn build(&mut self, expr: &syntax::Expr) {
        match expr.kind() {
            syntax::ExprKind::Integer(n) => {
                // Use standard macros for integer constant expression to expand
                // a value to the type int_least_N.
                self.push_str(format!("INT64_C({})", n));
            }
            syntax::ExprKind::Neg(a) => {
                self.push_str("-");
                self.build(a);
            }
            syntax::ExprKind::Add(a, b) => {
                self.push_str("(");
                self.build(a);
                self.push_str(" + ");
                self.build(b);
                self.push_str(")");
            }
            syntax::ExprKind::Sub(a, b) => {
                self.push_str("(");
                self.build(a);
                self.push_str(" - ");
                self.build(b);
                self.push_str(")");
            }
            syntax::ExprKind::Mul(a, b) => {
                self.push_str("(");
                self.build(a);
                self.push_str(" * ");
                self.build(b);
                self.push_str(")");
            }
            syntax::ExprKind::Div(a, b) => {
                self.push_str("(");
                self.build(a);
                self.push_str(" / ");
                self.build(b);
                self.push_str(")");
            }
            syntax::ExprKind::Var(name) => {
                self.push_str(name);
            }
            syntax::ExprKind::Call(name, args) => {
                self.push_str(name);
                self.push_str("(");
                for (i, arg) in args.iter().enumerate() {
                    self.build(arg);

                    if i != (args.len() - 1) {
                        self.push_str(", ");
                    }
                }
                self.push_str(")");
            }
            syntax::ExprKind::Puts(args) => {
                // "puts" function prints each arguments and newline character.
                self.push_str("printf(\"");
                for (i, _) in args.iter().enumerate() {
                    // Use standard conversion specifier macros for integer types.
                    self.push_str("%\" PRId64 \"");

                    if i != (args.len() - 1) {
                        self.push_str(", ");
                    }
                }
                self.push_str("\\n\", ");

                for (i, arg) in args.iter().enumerate() {
                    self.build(arg);

                    if i != (args.len() - 1) {
                        self.push_str(", ");
                    }
                }
                self.push_str(");");
                self.push_str("\n");
            }
            syntax::ExprKind::Let { name, rhs, then } => {
                self.push_str("int64_t ");
                self.push_str(name);
                self.push_str(" = ");
                self.build(rhs);
                self.push_str(";");
                self.push_str("\n");
                self.push_str("  ");
                self.build(then);
            }
            syntax::ExprKind::Fn {
                name,
                args,
                body,
                then,
            } => {
                let t = self.in_top_level;
                self.in_top_level = false;

                // comments
                // TODO: Currently, only leading comments of "def" supported.
                for c in expr.comments() {
                    self.push_str("//");
                    self.push_str(c);
                    self.push_str("\n");
                }

                self.push_str("int64_t ");
                self.push_str(name);
                self.push_str("(");
                for (i, arg) in args.iter().enumerate() {
                    self.push_str("int64_t ");
                    self.push_str(arg);

                    if i != (args.len() - 1) {
                        self.push_str(", ");
                    }
                }
                self.push_str(")\n");
                self.push_str("{");
                self.push_str("\n");
                self.push_str("  ");
                {
                    self.push_str("return ");
                    self.build(body);
                    self.push_str(";");
                    self.push_str("\n");
                }
                self.push_str("}");
                self.push_str("\n");
                self.push_str("  ");

                self.in_top_level = t;
                self.build(then);
            }
            syntax::ExprKind::Case { .. } => {
                todo!()
            }
        }
    }
}

pub fn emit(ast: &sem::SemAST) -> String {
    let mut emitter = Emitter::new();

    emitter.build(ast.expr());
    emitter.emit()
}
