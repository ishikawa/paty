//! WebAssembly backend which emits WAT (WebAssembly Text Format).
pub mod builder;

use self::builder::{
    DataSegment, Entity, Export, ExportDesc, Function, FunctionSignature, Import, ImportDesc,
    Index, Instruction, MemArg, Module, StringData, Type, WatBuilder,
};
use crate::ir::inst::Program;

/// WebAssembly has 32-bit and 64-bit architecture variants,
/// called wasm32 and wasm64. wasm32 has an ILP32 data model,
/// meaning that int, long, and pointer types are all 32-bit,
/// while the long long type is 64-bit. wasm64 has an LP64 data model,
/// meaning that long and pointer types will be 64-bit,
/// while int is 32-bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WasmArch {
    Bits32 = 32,
    Bits64 = 64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EmitterOptions {
    pub arch: WasmArch,
    /// Supports WASI (WebAssembly System Interface) or not.
    pub wasi: bool,
}

#[derive(Debug)]
pub struct Emitter {
    options: EmitterOptions,
}

impl Emitter {
    pub fn new(options: EmitterOptions) -> Self {
        Self { options }
    }

    pub fn emit<'a, 'tcx>(&mut self, _program: &'a Program<'a, 'tcx>) -> String {
        let mut module = Module::new();

        // -- imports
        if self.options.wasi {
            // fd_write(fd: fd, iovs: ciovec_array) -> Result<size, errno>
            let fun_fd_write = FunctionSignature::new(
                vec![
                    Entity::named("fd".into(), Type::I32),
                    Entity::named("iovs".into(), Type::I32),
                    Entity::named("iovs_len".into(), Type::I32),
                    Entity::named("nwritten".into(), Type::I32),
                ],
                vec![Type::I32],
            );

            module.push_import(Import::new(
                "wasi_snapshot_preview1".into(),
                "fd_write".into(),
                ImportDesc::Function(Entity::named("fd_write".into(), fun_fd_write)),
            ));
        }

        // -- exports
        module.push_export(Export::new(
            "memory".into(),
            ExportDesc::Memory(Index::Index(0)),
        ));

        // -- data segments
        module.push_data_segment(Entity::new(DataSegment::new(
            vec![Instruction::I32Const(8)],
            vec![StringData::String("hello world\n".to_string())],
        )));

        // -- functions
        {
            let mut main_fun = Function::new();

            // (i32.store (i32.const 0) (i32.const 8))  ;; iov.iov_base - This is a pointer to the start of the 'hello world\n' string
            main_fun.push_instruction(Instruction::I32Const(0));
            main_fun.push_instruction(Instruction::I32Const(8));
            main_fun.push_instruction(Instruction::I32Store(MemArg::default()));

            // (i32.store (i32.const 4) (i32.const 12))  ;; iov.iov_len - The length of the 'hello world\n' string
            main_fun.push_instruction(Instruction::I32Const(4));
            main_fun.push_instruction(Instruction::I32Const(12));
            main_fun.push_instruction(Instruction::I32Store(MemArg::default()));

            // (call $fd_write
            //     (i32.const 1) ;; file_descriptor - 1 for stdout
            //     (i32.const 0) ;; *iovs - The pointer to the iov array, which is stored at memory location 0
            //     (i32.const 1) ;; iovs_len - We're printing 1 string stored in an iov - so one.
            //     (i32.const 20) ;; nwritten - A place in memory to store the number of bytes written
            // )
            main_fun.push_instruction(Instruction::I32Const(1));
            main_fun.push_instruction(Instruction::I32Const(0));
            main_fun.push_instruction(Instruction::I32Const(1));
            main_fun.push_instruction(Instruction::I32Const(24));
            main_fun.push_instruction(Instruction::Call(Index::Id("fd_write".into())));

            // drop ;; Discard the number of bytes written from the top of the stack
            main_fun.push_instruction(Instruction::Drop);

            module.push_function(Entity::named("main".into(), main_fun));
        }

        // -- build
        let mut wat = WatBuilder::new();
        wat.emit(&Entity::named("demo.wat".into(), module))
    }
}
