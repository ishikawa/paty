use chumsky::Parser;
use paty::gen;
use paty::sem;
use paty::syntax;
use std::env;
use std::fs;
use typed_arena::Arena;

fn main() {
    let filepath = env::args().nth(1).expect("filename");
    let src = fs::read_to_string(filepath).expect("Read source code");
    eprintln!("---\n{}", src);

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

    {
        let expr_arena = Arena::new();
        let tmp_var_arena = Arena::new();

        let mut builder = gen::ir::Builder::new(&expr_arena, &tmp_var_arena);
        let program = builder.build(&ast);
        eprintln!("---\n{}", program);

        let mut emitter = gen::c::Emitter::new();
        let code = emitter.emit(&program);

        //eprintln!("-----\n{}-----", code);
        println!("{}", code);
    }
}
