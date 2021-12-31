//! Semantic analysis
use crate::syntax;

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
    match expr {
        syntax::Expr::Integer(_) => Ok(()),
        syntax::Expr::Neg(a) => analyze_loop(a, vars, functions),
        syntax::Expr::Add(a, b)
        | syntax::Expr::Sub(a, b)
        | syntax::Expr::Mul(a, b)
        | syntax::Expr::Div(a, b) => {
            analyze_loop(a, vars, functions)?;
            analyze_loop(b, vars, functions)
        }
        syntax::Expr::Var(name) => {
            if vars.iter().rev().any(|var| *var == name) {
                Ok(())
            } else {
                Err(format!("Cannot find variable `{}` in scope", name))
            }
        }
        syntax::Expr::Let { name, rhs, then } => {
            analyze_loop(rhs, vars, functions)?;

            vars.push(name);
            let output = analyze_loop(then, vars, functions);
            vars.pop();
            output
        }
        syntax::Expr::Call(name, args) => {
            if let Some((_, arg_names, body)) = functions
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

                for arg in arg_names {
                    vars.push(arg);
                }

                let output = analyze_loop(body, vars, functions);
                vars.truncate(vars.len() - arg_names.len());
                output
            } else {
                Err(format!("Cannot find function `{}` in scope", name))
            }
        }
        syntax::Expr::Puts(args) => {
            for arg in args {
                analyze_loop(arg, vars, functions)?;
            }
            Ok(())
        }
        syntax::Expr::Fn {
            name,
            args,
            body,
            then,
        } => {
            functions.push((name, args, body));
            let output = analyze_loop(then, vars, functions);
            functions.pop();
            output
        }
    }
}
