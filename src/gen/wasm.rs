//! WebAssembly backend which emits WAT (WebAssembly Text Format).
pub mod builder;

use self::builder::{
    DataSegment, Entity, Export, ExportDesc, FunctionSignature, Import, ImportDesc, Index,
    Instruction, Module, StringData, Type, WatBuilder,
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

        let mut wat = WatBuilder::new();

        wat.emit(&Entity::named("demo.wat".into(), module))
    }
}
