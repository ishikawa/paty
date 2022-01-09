//! Semantic analysis
use crate::{syntax, typing::Type};

use self::error::SemanticError;
mod error;
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
pub fn analyze(expr: &syntax::Expr) -> Result<SemAST, Vec<SemanticError>> {
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
    errors: &mut Vec<SemanticError>,
) {
    match expr.kind() {
        syntax::ExprKind::Integer(_) => {}
        syntax::ExprKind::Boolean(_) => {}
        syntax::ExprKind::Minus(a) => analyze_loop(a, vars, functions, errors),
        syntax::ExprKind::Add(a, b)
        | syntax::ExprKind::Sub(a, b)
        | syntax::ExprKind::Mul(a, b)
        | syntax::ExprKind::Div(a, b)
        | syntax::ExprKind::Eq(a, b)
        | syntax::ExprKind::Ne(a, b)
        | syntax::ExprKind::Lt(a, b)
        | syntax::ExprKind::Gt(a, b)
        | syntax::ExprKind::Le(a, b)
        | syntax::ExprKind::Ge(a, b)
        | syntax::ExprKind::And(a, b)
        | syntax::ExprKind::Or(a, b) => {
            analyze_loop(a, vars, functions, errors);
            analyze_loop(b, vars, functions, errors)
        }
        syntax::ExprKind::Var(name) => {
            if !vars.iter().rev().any(|var| *var == name) {
                errors.push(SemanticError::UndefinedVariable { name: name.clone() });
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
                    errors.push(SemanticError::WrongNumberOfArguments {
                        name: name.clone(),
                        expected: arg_names.len(),
                        actual: args.len(),
                    });
                } else {
                    for arg in args {
                        analyze_loop(arg, vars, functions, errors);
                    }
                }
            } else {
                errors.push(SemanticError::UndefinedFunction { name: name.clone() });
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

            // TODO: type inference
            let head_ty = if matches!(
                head.kind(),
                syntax::ExprKind::Boolean(_)
                    | syntax::ExprKind::Eq(_, _)
                    | syntax::ExprKind::Ne(_, _)
                    | syntax::ExprKind::Le(_, _)
                    | syntax::ExprKind::Ge(_, _)
                    | syntax::ExprKind::Lt(_, _)
                    | syntax::ExprKind::Gt(_, _)
                    | syntax::ExprKind::And(_, _)
                    | syntax::ExprKind::Or(_, _)
            ) {
                Type::Boolean
            } else {
                Type::Int64
            };

            if let Err(err) = usefulness::check_match(head_ty, arms, else_body.is_some()) {
                errors.extend(err);
            }
        }
    }
}
