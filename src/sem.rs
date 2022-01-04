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
pub fn analyze(expr: &syntax::Expr) -> Result<SemAST, String> {
    analyze_loop(expr, &mut Vec::new(), &mut Vec::new())?;
    Ok(SemAST::new(expr))
}

fn analyze_loop<'a>(
    expr: &'a syntax::Expr,
    vars: &mut Vec<&'a String>,
    functions: &mut Vec<(&'a String, &'a [String], &'a syntax::Expr)>,
) -> Result<(), String> {
    match expr.kind() {
        syntax::ExprKind::Integer(_) => Ok(()),
        syntax::ExprKind::Neg(a) => analyze_loop(a, vars, functions),
        syntax::ExprKind::Add(a, b)
        | syntax::ExprKind::Sub(a, b)
        | syntax::ExprKind::Mul(a, b)
        | syntax::ExprKind::Div(a, b) => {
            analyze_loop(a, vars, functions)?;
            analyze_loop(b, vars, functions)
        }
        syntax::ExprKind::Var(name) => {
            if vars.iter().rev().any(|var| *var == name) {
                Ok(())
            } else {
                Err(format!("Cannot find variable `{}` in scope", name))
            }
        }
        syntax::ExprKind::Let { name, rhs, then } => {
            analyze_loop(rhs, vars, functions)?;

            vars.push(name);
            let output = analyze_loop(then, vars, functions);
            vars.pop();
            output
        }
        syntax::ExprKind::Call(name, args) => {
            if let Some((_, arg_names, _)) = functions
                .iter()
                .rev()
                .find(|(var, _, _)| *var == name)
                .copied()
            {
                if arg_names.len() != args.len() {
                    return Err(format!(
                        "Wrong number of arguments for function `{}`: expected {}, found {}",
                        name,
                        arg_names.len(),
                        args.len(),
                    ));
                }

                for arg in args {
                    analyze_loop(arg, vars, functions)?;
                }

                Ok(())
            } else {
                Err(format!("Cannot find function `{}` in scope", name))
            }
        }
        syntax::ExprKind::Puts(args) => {
            for arg in args {
                analyze_loop(arg, vars, functions)?;
            }
            Ok(())
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
                    analyze_loop(body, vars, functions)?;
                }
                vars.truncate(vars.len() - args.len());
                analyze_loop(then, vars, functions)?;
            }
            functions.pop();
            Ok(())
        }
        syntax::ExprKind::Case {
            head,
            arms,
            else_body,
        } => {
            analyze_loop(head, vars, functions)?;

            for arm in arms {
                analyze_loop(arm.body(), vars, functions)?;
            }

            if let Some(else_body) = else_body {
                analyze_loop(else_body, vars, functions)?;
            }

            usefulness::check_match(arms);

            Ok(())
        }
    }
}
