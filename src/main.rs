use chumsky::Parser;
use paty::sem;
use paty::syntax;
use std::env;
use std::fs;

fn main() {
    let filepath = env::args().nth(1).expect("filename");
    let src = fs::read_to_string(filepath).expect("Read source code");

    let tokens = match syntax::lexer().parse(src) {
        Err(err) => {
            err.into_iter()
                .for_each(|e| eprintln!("Syntax error: {}", e));
            std::process::exit(exitcode::DATAERR);
        }
        Ok(tokens) => tokens,
    };
    //println!("tokens = {:?}", tokens);

    let expr = match syntax::parser().parse(tokens) {
        Err(err) => {
            err.into_iter()
                .for_each(|e| eprintln!("Parse error: {}", e));
            std::process::exit(exitcode::DATAERR);
        }
        Ok(expr) => expr,
    };
    //println!("ast = {:?}", expr);

    let ast = match sem::analyze(&expr) {
        Err(errors) => {
            assert!(!errors.is_empty());

            for err in errors {
                eprintln!("Semantic error: {}", err);
            }

            std::process::exit(exitcode::DATAERR);
        }
        Ok(ast) => ast,
    };

    let code = paty::c::emit(&ast);
    println!("{}", code);
}
