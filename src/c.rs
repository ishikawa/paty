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
            "#include <stdio.h>\n\n",
            &self.functions,
            "\n",
            "int main(void)\n{\n",
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
        match expr {
            syntax::Expr::Integer(x) => {
                self.push_str(x.to_string());
            }
            syntax::Expr::Neg(a) => {
                self.push_str("-");
                self.build(a);
            }
            syntax::Expr::Add(a, b) => {
                self.build(a);
                self.push_str(" + ");
                self.build(b);
            }
            syntax::Expr::Sub(a, b) => {
                self.build(a);
                self.push_str(" - ");
                self.build(b);
            }
            syntax::Expr::Mul(a, b) => {
                self.build(a);
                self.push_str(" * ");
                self.build(b);
            }
            syntax::Expr::Div(a, b) => {
                self.build(a);
                self.push_str(" / ");
                self.build(b);
            }
            syntax::Expr::Var(name) => {
                self.push_str(name);
            }
            syntax::Expr::Call(name, args) => {
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
            syntax::Expr::Puts(args) => {
                // "puts" function prints each arguments and newline character.
                self.push_str("printf(\"");
                for (i, _) in args.iter().enumerate() {
                    self.push_str("%d");

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
            syntax::Expr::Let { name, rhs, then } => {
                self.push_str("int ");
                self.push_str(name);
                self.push_str(" = ");
                self.build(rhs);
                self.push_str(";");
                self.push_str("\n");
                self.push_str("  ");
                self.build(then);
            }
            syntax::Expr::Fn {
                name,
                args,
                body,
                then,
            } => {
                let t = self.in_top_level;
                self.in_top_level = false;

                self.push_str("int ");
                self.push_str(name);
                self.push_str("(");
                for (i, arg) in args.iter().enumerate() {
                    self.push_str("int ");
                    self.push_str(arg);

                    if i != (args.len() - 1) {
                        self.push_str(", ");
                    }
                }
                self.push_str(") \n");
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
        }
    }
}

pub fn emit(ast: &sem::SemAST) -> String {
    let mut emitter = Emitter::new();

    emitter.build(ast.expr());
    emitter.emit()
}
