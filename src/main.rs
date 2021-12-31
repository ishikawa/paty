use chumsky::Parser;
use std::env;
use std::fs;

fn main() {
    let filepath = env::args().nth(1).expect("filename");
    let src = fs::read_to_string(filepath).expect("Read source code");

    let tokens = match paty::lexer().parse(src) {
        Err(err) => {
            err.into_iter()
                .for_each(|e| eprintln!("Syntax error: {}", e));
            std::process::exit(exitcode::DATAERR);
        }
        Ok(tokens) => tokens,
    };
    //println!("tokens = {:?}", tokens);

    let ast = match paty::parser().parse(tokens) {
        Err(err) => {
            err.into_iter()
                .for_each(|e| eprintln!("Parse error: {}", e));
            std::process::exit(exitcode::DATAERR);
        }
        Ok(ast) => ast,
    };
    //println!("ast = {:?}", ast);

    match paty::eval(&ast) {
        Ok(_result) => {
            //println!("{}", result);
        }
        Err(err) => {
            eprintln!("Evaluation error: {}", err);
            std::process::exit(exitcode::UNAVAILABLE);
        }
    };
}
