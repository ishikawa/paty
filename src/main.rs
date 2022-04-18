use clap::Parser;
use paty::gen;
use paty::ir;
use paty::ir::optimizer;
use paty::sem;
use paty::syntax;
use paty::ty::TypeContext;
use std::fs;
use std::io;
use std::io::Read;
use std::str::FromStr;
use typed_arena::Arena;

const MAX_OPTIMIZATION_REPEAT: usize = 8;

const TARGET_NAME_TO_VARIANTS: [(&str, Target); 6] = [
    ("c", Target::C),
    (
        "wasm",
        Target::Wasm(gen::wasm::EmitterOptions {
            arch: gen::wasm::WasmArch::Bits32,
            wasi: false,
        }),
    ),
    (
        "wasm32",
        Target::Wasm(gen::wasm::EmitterOptions {
            arch: gen::wasm::WasmArch::Bits32,
            wasi: false,
        }),
    ),
    (
        "wasm64",
        Target::Wasm(gen::wasm::EmitterOptions {
            arch: gen::wasm::WasmArch::Bits64,
            wasi: false,
        }),
    ),
    (
        "wasm32-wasi",
        Target::Wasm(gen::wasm::EmitterOptions {
            arch: gen::wasm::WasmArch::Bits32,
            wasi: true,
        }),
    ),
    (
        "wasm64-wasi",
        Target::Wasm(gen::wasm::EmitterOptions {
            arch: gen::wasm::WasmArch::Bits64,
            wasi: true,
        }),
    ),
];

const TARGET_OPTION_POSSIBLE_VALUES: [&str; TARGET_NAME_TO_VARIANTS.len()] = [
    TARGET_NAME_TO_VARIANTS[0].0,
    TARGET_NAME_TO_VARIANTS[1].0,
    TARGET_NAME_TO_VARIANTS[2].0,
    TARGET_NAME_TO_VARIANTS[3].0,
    TARGET_NAME_TO_VARIANTS[4].0,
    TARGET_NAME_TO_VARIANTS[5].0,
];

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Target {
    /// C language
    C,
    /// WebAssembly
    Wasm(gen::wasm::EmitterOptions),
}

impl FromStr for Target {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        TARGET_NAME_TO_VARIANTS
            .iter()
            .find(|(name, _)| *name == s)
            .map(|(_, target)| target.clone())
            .ok_or_else(|| format!("Unrecognized input: {}", s))
    }
}

#[derive(clap::Parser, Debug)]
#[clap(version)]
struct Args {
    /// Choose a compile target for emitting code.
    #[clap(
        long,
        default_value = TARGET_OPTION_POSSIBLE_VALUES[0],
        possible_values=TARGET_OPTION_POSSIBLE_VALUES)]
    target: Target,

    /// Source code file to read.
    #[clap(required = false)]
    file: Option<String>,
}

fn main() {
    let args = Args::parse();

    // Read input: use STDIN if no positional argument to point to the file.
    let src = if let Some(filename) = args.file {
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

    let body = match parser.parse(&tokens) {
        Err(err) => {
            eprintln!("Parse error: {}", err);
            std::process::exit(exitcode::DATAERR);
        }
        Ok(body) => body,
    };
    //eprintln!("Syntax tree = {:#?}", body);

    if let Err(errors) = sem::analyze(tcx, &body) {
        assert!(!errors.is_empty());

        for err in errors {
            eprintln!("Semantic error: {}", err);
        }

        std::process::exit(exitcode::DATAERR);
    }
    //eprintln!("--- Syntax tree (not optimized)\n{:?}", &body);

    {
        let ir_expr_arena = Arena::new();
        let ir_stmt_arena = Arena::new();
        let tmp_var_arena = Arena::new();

        let builder =
            ir::builder::Builder::new(tcx, &ir_expr_arena, &ir_stmt_arena, &tmp_var_arena);
        let mut program = builder.build(&body);

        // post process
        let optimizer = optimizer::Optimizer::new(tcx, &ir_expr_arena, &ir_stmt_arena);

        // Repeat (up to 5 times) the process of replacing the temporary variables
        // until there is no change in the optimized code.
        for i in 0..MAX_OPTIMIZATION_REPEAT {
            let mut changed = false;
            let pass = optimizer::MarkTmpVarUsed::default();
            optimizer
                .run_function_pass(&pass, &mut program)
                .then(|| changed = true);
            //eprintln!("--- (optimizing:{})\n{}", i, program);

            let pass = optimizer::UpdateTmpVarValue::default();
            optimizer
                .run_function_pass(&pass, &mut program)
                .then(|| changed = true);
            let pass = optimizer::EliminateDeadStmts::default();
            optimizer
                .run_function_pass(&pass, &mut program)
                .then(|| changed = true);
            let pass = optimizer::ReplaceRedundantTmpVars::default();
            optimizer
                .run_function_pass(&pass, &mut program)
                .then(|| changed = true);
            if !changed {
                break;
            }

            // reset used count if next loop
            if i + 1 < MAX_OPTIMIZATION_REPEAT {
                let pass = optimizer::ResetTmpVarUsed::default();
                optimizer
                    .run_function_pass(&pass, &mut program)
                    .then(|| changed = true);
            }
        }

        let pass = optimizer::ConcatAdjacentPrintf::default();
        optimizer.run_function_pass(&pass, &mut program);
        //eprintln!("--- (optimized)\n{}", program);

        match args.target {
            Target::C => {
                let mut emitter = gen::c::Emitter::new();
                let code = emitter.emit(&program);

                println!("{}", code);
            }
            Target::Wasm(options) => {
                let mut emitter = gen::wasm::Emitter::new(options);
                let code = emitter.emit(&program);

                println!("{}", code);
            }
        }
    }
}
