use paty::gen;
use paty::sem;
use paty::syntax;
use paty::ty::TypeContext;
use std::env;
use std::fs;
use std::io;
use std::io::Read;
use typed_arena::Arena;

fn main() {
    // Read input: use STDIN if no positional argument to point to the file.
    let src = if let Some(filename) = env::args().nth(1) {
        fs::read_to_string(filename).expect("Read source code")
    } else {
        let mut src = String::new();
        let stdin = io::stdin();

        stdin
            .lock()
            .read_to_string(&mut src)
            .expect("Read source code");
        src
    };
    //eprintln!("---\n{}", src);

    let tokens = match syntax::tokenize(&src) {
        Err(err) => {
            err.into_iter()
                .for_each(|e| eprintln!("Syntax error: {}", e));
            std::process::exit(exitcode::DATAERR);
        }
        Ok(tokens) => tokens,
    };

    //eprintln!("tokens = {:?}", tokens);
    let type_arena = Arena::new();
    let tcx = TypeContext::new(&type_arena);

    let ast_expr_arena = Arena::new();
    let ast_pat_arena = Arena::new();
    let parser = syntax::Parser::new(tcx, &ast_expr_arena, &ast_pat_arena);

    let expr = match parser.parse(&tokens) {
        Err(err) => {
            eprintln!("Parse error: {}", err);
            std::process::exit(exitcode::DATAERR);
        }
        Ok(expr) => expr,
    };
    //println!("ast = {:?}", expr);

    let ast = match sem::analyze(tcx, expr) {
        Err(errors) => {
            assert!(!errors.is_empty());

            for err in errors {
                eprintln!("Semantic error: {}", err);
            }

            std::process::exit(exitcode::DATAERR);
        }
        Ok(ast) => ast,
    };
    //eprintln!("ast = {:?}", ast);

    {
        let ir_expr_arena = Arena::new();
        let tmp_var_arena = Arena::new();

        let mut builder = gen::ir::Builder::new(tcx, &ir_expr_arena, &tmp_var_arena);
        let program = builder.build(&ast);
        //eprintln!("---\n{}", program);

        let mut emitter = gen::c::Emitter::new();
        let code = emitter.emit(&program);

        //eprintln!("-----\n{}-----", code);
        println!("{}", code);
    }
}
