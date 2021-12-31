use chumsky::Parser;
use std::env;
use std::fs;

fn main() {
    let filepath = env::args().nth(1).expect("filename");
    let src = fs::read_to_string(filepath).expect("Read source code");

    match paty::parser().parse(src) {
        Ok(ast) => match paty::eval(&ast, &mut Vec::new(), &mut Vec::new()) {
            Ok(output) => println!("{}", output),
            Err(err) => println!("Evaluation error: {}", err),
        },
        Err(err) => err.into_iter().for_each(|e| println!("Parse error: {}", e)),
    }
}
