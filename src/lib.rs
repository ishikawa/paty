pub mod c;
pub mod sem;
pub mod syntax;

pub fn eval(expr: &syntax::Expr) -> Result<i64, String> {
    eval_loop(expr, &mut Vec::new(), &mut Vec::new())
}

fn eval_loop<'a>(
    expr: &'a syntax::Expr,
    vars: &mut Vec<(&'a String, i64)>,
    functions: &mut Vec<(&'a String, &'a [String], &'a syntax::Expr)>,
) -> Result<i64, String> {
    match expr {
        syntax::Expr::Integer(x) => Ok(*x),
        syntax::Expr::Neg(a) => Ok(-eval_loop(a, vars, functions)?),
        syntax::Expr::Add(a, b) => {
            Ok(eval_loop(a, vars, functions)? + eval_loop(b, vars, functions)?)
        }
        syntax::Expr::Sub(a, b) => {
            Ok(eval_loop(a, vars, functions)? - eval_loop(b, vars, functions)?)
        }
        syntax::Expr::Mul(a, b) => {
            Ok(eval_loop(a, vars, functions)? * eval_loop(b, vars, functions)?)
        }
        syntax::Expr::Div(a, b) => {
            Ok(eval_loop(a, vars, functions)? / eval_loop(b, vars, functions)?)
        }
        syntax::Expr::Var(name) => {
            if let Some((_, val)) = vars.iter().rev().find(|(var, _)| *var == name) {
                Ok(*val)
            } else {
                Err(format!("Cannot find variable `{}` in scope", name))
            }
        }
        syntax::Expr::Let { name, rhs, then } => {
            let rhs = eval_loop(rhs, vars, functions)?;
            vars.push((name, rhs));
            let output = eval_loop(then, vars, functions);
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
                if arg_names.len() == args.len() {
                    let mut args = args
                        .iter()
                        .map(|arg| eval_loop(arg, vars, functions))
                        .zip(arg_names.iter())
                        .map(|(val, name)| Ok((name, val?)))
                        .collect::<Result<_, String>>()?;
                    vars.append(&mut args);
                    let output = eval_loop(body, vars, functions);
                    vars.truncate(vars.len() - args.len());
                    output
                } else {
                    Err(format!(
                        "Wrong number of arguments for function `{}`: expected {}, found {}",
                        name,
                        arg_names.len(),
                        args.len(),
                    ))
                }
            } else {
                Err(format!("Cannot find function `{}` in scope", name))
            }
        }
        syntax::Expr::Puts(args) => {
            // "puts" function prints each arguments and newline character.
            for (i, arg) in args.iter().enumerate() {
                let v = eval_loop(arg, vars, functions)?;

                print!("{}", v);
                if i != (args.len() - 1) {
                    print!(", ");
                }
            }
            println!();

            Ok(0) // no value
        }
        syntax::Expr::Fn {
            name,
            args,
            body,
            then,
        } => {
            functions.push((name, args, body));
            let output = eval_loop(then, vars, functions);
            functions.pop();
            output
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chumsky::Parser;

    #[test]
    fn number() {
        let val = eval_i64("20211231");
        assert_eq!(val, 20211231);
    }

    #[test]
    fn variable() {
        let val = eval_i64(
            "
            five = 5
            five",
        );
        assert_eq!(val, 5);
    }

    #[test]
    fn function() {
        let val = eval_i64(
            "
            def foo(x, y)
                x + y
            end
            foo(10, 20)",
        );
        assert_eq!(val, 30);
    }

    fn eval_i64(src: &str) -> i64 {
        let tokens = syntax::lexer().parse(src).unwrap();
        let ast = syntax::parser().parse(tokens).unwrap();

        eval(&ast).unwrap()
    }
}
