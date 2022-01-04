//! Semantic analysis
use crate::syntax;
mod usefulness;

#[derive(Debug)]
pub struct SemAST<'a> {
    expr: &'a syntax::Expr,
}

impl<'a> SemAST<'a> {
    pub fn new(expr: &'a syntax::Expr) -> Self {
        Self { expr }
    }

    pub fn expr(&self) -> &syntax::Expr {
        self.expr
    }
}

// Analyze an AST and returns error if any.
pub fn analyze(expr: &syntax::Expr) -> Result<SemAST, Vec<String>> {
    let mut errors = vec![];

    analyze_loop(expr, &mut Vec::new(), &mut Vec::new(), &mut errors);
    if errors.is_empty() {
        Ok(SemAST::new(expr))
    } else {
        Err(errors)
    }
}

fn analyze_loop<'a>(
    expr: &'a syntax::Expr,
    vars: &mut Vec<&'a String>,
    functions: &mut Vec<(&'a String, &'a [String], &'a syntax::Expr)>,
    errors: &mut Vec<String>,
) {
    match expr.kind() {
        syntax::ExprKind::Integer(_) => {}
        syntax::ExprKind::Neg(a) => analyze_loop(a, vars, functions, errors),
        syntax::ExprKind::Add(a, b)
        | syntax::ExprKind::Sub(a, b)
        | syntax::ExprKind::Mul(a, b)
        | syntax::ExprKind::Div(a, b) => {
            analyze_loop(a, vars, functions, errors);
            analyze_loop(b, vars, functions, errors)
        }
        syntax::ExprKind::Var(name) => {
            if !vars.iter().rev().any(|var| *var == name) {
                errors.push(format!("Cannot find variable `{}` in scope", name));
            }
        }
        syntax::ExprKind::Let { name, rhs, then } => {
            analyze_loop(rhs, vars, functions, errors);

            vars.push(name);
            analyze_loop(then, vars, functions, errors);
            vars.pop();
        }
        syntax::ExprKind::Call(name, args) => {
            if let Some((_, arg_names, _)) = functions
                .iter()
                .rev()
                .find(|(var, _, _)| *var == name)
                .copied()
            {
                if arg_names.len() != args.len() {
                    errors.push(format!(
                        "Wrong number of arguments for function `{}`: expected {}, found {}",
                        name,
                        arg_names.len(),
                        args.len(),
                    ));
                } else {
                    for arg in args {
                        analyze_loop(arg, vars, functions, errors);
                    }
                }
            } else {
                errors.push(format!("Cannot find function `{}` in scope", name));
            }
        }
        syntax::ExprKind::Puts(args) => {
            for arg in args {
                analyze_loop(arg, vars, functions, errors);
            }
        }
        syntax::ExprKind::Fn {
            name,
            args,
            body,
            then,
        } => {
            functions.push((name, args, body));
            {
                vars.extend(args);
                {
                    analyze_loop(body, vars, functions, errors);
                }
                vars.truncate(vars.len() - args.len());
                analyze_loop(then, vars, functions, errors);
            }
            functions.pop();
        }
        syntax::ExprKind::Case {
            head,
            arms,
            else_body,
        } => {
            analyze_loop(head, vars, functions, errors);

            for arm in arms {
                analyze_loop(arm.body(), vars, functions, errors);
            }

            if let Some(else_body) = else_body {
                analyze_loop(else_body, vars, functions, errors);
            }

            if !errors.is_empty() {
                return;
            }
            // Usefulness check

            usefulness::check_match(arms);
        }
    }
}
