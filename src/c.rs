//! C code generator
use crate::sem;
use crate::syntax;
use crate::syntax::PatternKind;

#[derive(Debug)]
struct Emitter {
    main: String,
    functions: String,
    in_top_level: bool,
    // The current index of temporary variables. It starts from 0 and
    // incremented by creating a new temporary variable. This index will
    // be saved and reset to 0 when function enter, and restored when function exit.
    tmp_var_index: i32,
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            main: String::default(),
            functions: String::default(),
            in_top_level: true,
            tmp_var_index: 0,
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
            &self.main,
            "return 0;\n",
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

    fn new_tmp_var(&mut self) -> i32 {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;

        self.push_str("int64_t ");
        self.push_str(format!("t{}", t));
        self.push_str(";\n");

        t
    }

    fn build(&mut self, expr: &syntax::Expr) -> i32 {
        match expr.kind() {
            syntax::ExprKind::Integer(n) => {
                let t = self.new_tmp_var();

                // Use standard macros for integer constant expression to expand
                // a value to the type int_least_N.
                self.push_str(format!("t{} = INT64_C({})", t, n));
                self.push_str(";\n");
                t
            }
            syntax::ExprKind::Minus(a) => {
                let t = self.new_tmp_var();
                let ta = self.build(a);
                self.push_str(format!("t{} = -t{}", t, ta));
                self.push_str(";\n");
                t
            }
            syntax::ExprKind::Add(a, b) => {
                let t = self.new_tmp_var();
                let ta = self.build(a);
                let tb = self.build(b);
                self.push_str(format!("t{} = t{} + t{}", t, ta, tb));
                self.push_str(";\n");
                t
            }
            syntax::ExprKind::Sub(a, b) => {
                let t = self.new_tmp_var();
                let ta = self.build(a);
                let tb = self.build(b);
                self.push_str(format!("t{} = t{} - t{}", t, ta, tb));
                self.push_str(";\n");
                t
            }
            syntax::ExprKind::Mul(a, b) => {
                let t = self.new_tmp_var();
                let ta = self.build(a);
                let tb = self.build(b);
                self.push_str(format!("t{} = t{} * t{}", t, ta, tb));
                self.push_str(";\n");
                t
            }
            syntax::ExprKind::Div(a, b) => {
                let t = self.new_tmp_var();
                let ta = self.build(a);
                let tb = self.build(b);
                self.push_str(format!("t{} = t{} / t{}", t, ta, tb));
                self.push_str(";\n");
                t
            }
            syntax::ExprKind::Var(name) => {
                let t = self.new_tmp_var();
                self.push_str(format!("t{} = {}", t, name));
                self.push_str(";\n");
                t
            }
            syntax::ExprKind::Call(name, args) => {
                let mut t_args = vec![];
                let t = self.new_tmp_var();

                for arg in args.iter() {
                    t_args.push(self.build(arg));
                }
                self.push_str(format!("t{} = {}(", t, name));
                for (i, ta) in t_args.iter().enumerate() {
                    // Use standard conversion specifier macros for integer types.
                    self.push_str(format!("t{}", ta));

                    if i != (args.len() - 1) {
                        self.push_str(", ");
                    }
                }
                self.push_str(")");
                self.push_str(";\n");

                t
            }
            syntax::ExprKind::Puts(args) => {
                // "puts" function prints each arguments and newline character.
                let mut t_args = vec![];

                for arg in args.iter() {
                    t_args.push(self.build(arg));
                }

                self.push_str("printf(\"");
                for (i, _) in args.iter().enumerate() {
                    // Use standard conversion specifier macros for integer types.
                    self.push_str("%\" PRId64 \"");

                    if i != (args.len() - 1) {
                        self.push_str(", ");
                    }
                }
                self.push_str("\\n\", ");

                for (i, ta) in t_args.iter().enumerate() {
                    self.push_str(format!("t{}", ta));

                    if i != (args.len() - 1) {
                        self.push_str(", ");
                    }
                }
                self.push_str(")");
                self.push_str(";\n");

                // dummy
                0
            }
            syntax::ExprKind::Let { name, rhs, then } => {
                let tr = self.build(rhs);

                self.push_str("int64_t ");
                self.push_str(name);
                self.push_str(format!(" = t{}", tr));
                self.push_str(";\n");
                self.build(then)
            }
            syntax::ExprKind::Fn {
                name,
                args,
                body,
                then,
            } => {
                // save and reset top level flag
                let saved_in_top_level = self.in_top_level;
                self.in_top_level = false;

                // save and reset temp var index
                let saved_tmp_var_index = self.tmp_var_index;
                self.tmp_var_index = 0;

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
                self.push_str("{\n");
                {
                    let tb = self.build(body);

                    self.push_str(format!("return t{}", tb));
                    self.push_str(";");
                    self.push_str("\n");
                }
                self.push_str("}\n");

                // restore
                self.in_top_level = saved_in_top_level;
                self.tmp_var_index = saved_tmp_var_index;
                self.build(then)
            }
            syntax::ExprKind::Case {
                head,
                arms,
                else_body,
            } => {
                let t = self.new_tmp_var();
                let t_head = self.build(head);

                // Construct "if-else" statement from each branches.
                for (i, arm) in arms.iter().enumerate() {
                    // Build an immediate value from the pattern
                    let condition = match arm.pattern().kind() {
                        PatternKind::Integer(n) => format!("t{} == INT64_C({})", t_head, n),
                        PatternKind::Range { lo, hi, end } => match end {
                            syntax::RangeEnd::Included => format!(
                                "t{} >= INT64_C({}) && t{} <= INT64_C({})",
                                t_head, lo, t_head, hi
                            ),
                            syntax::RangeEnd::Excluded => format!(
                                "t{} >= INT64_C({}) && t{} < INT64_C({})",
                                t_head, lo, t_head, hi
                            ),
                        },
                        PatternKind::Wildcard => "1".to_string(),
                    };

                    // Build "if" statement
                    if i > 0 {
                        self.push_str("else ");
                    }
                    self.push_str(format!("if ({}) {{\n", condition));
                    let t_body = self.build(arm.body());
                    self.push_str(format!("t{} = t{}", t, t_body));
                    self.push_str(";\n");
                    self.push_str("}\n");
                }
                if let Some(else_body) = else_body {
                    self.push_str("else {");
                    let t_body = self.build(else_body);
                    self.push_str(format!("t{} = t{}", t, t_body));
                    self.push_str(";\n");
                    self.push_str("}\n");
                }

                t
            }
        }
    }
}

pub fn emit(ast: &sem::SemAST) -> String {
    let mut emitter = Emitter::new();

    emitter.build(ast.expr());
    emitter.emit()
}
