pub mod sem;
pub mod syntax;

pub fn eval(ast: &sem::SemAST) -> i64 {
    eval_loop(ast.expr(), &mut Vec::new(), &mut Vec::new())
}

fn eval_loop<'a>(
    expr: &'a syntax::Expr,
    vars: &mut Vec<(&'a String, i64)>,
    functions: &mut Vec<(&'a String, &'a [String], &'a syntax::Expr)>,
) -> i64 {
    match expr {
        syntax::Expr::Integer(x) => *x,
        syntax::Expr::Neg(a) => -eval_loop(a, vars, functions),
        syntax::Expr::Add(a, b) => eval_loop(a, vars, functions) + eval_loop(b, vars, functions),
        syntax::Expr::Sub(a, b) => eval_loop(a, vars, functions) - eval_loop(b, vars, functions),
        syntax::Expr::Mul(a, b) => eval_loop(a, vars, functions) * eval_loop(b, vars, functions),
        syntax::Expr::Div(a, b) => eval_loop(a, vars, functions) / eval_loop(b, vars, functions),
        syntax::Expr::Var(name) => {
            let (_, val) = vars
                .iter()
                .rev()
                .find(|(var, _)| *var == name)
                .unwrap_or_else(|| panic!("var {}", name));
            *val
        }
        syntax::Expr::Let { name, rhs, then } => {
            let rhs = eval_loop(rhs, vars, functions);
            vars.push((name, rhs));
            let output = eval_loop(then, vars, functions);
            vars.pop();
            output
        }
        syntax::Expr::Call(name, args) => {
            let (_, arg_names, body) = functions
                .iter()
                .rev()
                .find(|(var, _, _)| *var == name)
                .copied()
                .expect("function");

            assert_eq!(arg_names.len(), args.len(), "argument count");

            let mut args = args
                .iter()
                .map(|arg| eval_loop(arg, vars, functions))
                .zip(arg_names.iter())
                .map(|(val, name)| (name, val))
                .collect::<_>();

            vars.append(&mut args);
            let output = eval_loop(body, vars, functions);
            vars.truncate(vars.len() - args.len());
            output
        }
        syntax::Expr::Puts(args) => {
            // "puts" function prints each arguments and newline character.
            for (i, arg) in args.iter().enumerate() {
                let v = eval_loop(arg, vars, functions);

                print!("{}", v);
                if i != (args.len() - 1) {
                    print!(", ");
                }
            }
            println!();
            0 // no value
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
        let expr = syntax::parser().parse(tokens).unwrap();
        let ast = sem::analyze(&expr).unwrap();

        eval(&ast)
    }
}
