//! WebAssembly
//! https://webassembly.github.io/spec/core/intro/introduction.html

use std::fmt;

/// Various entities in WebAssembly are classified by types.
/// Types are checked during validation, instantiation, and
/// possibly execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    // Number Types
    // The types  and  classify 32 and 64 bit integers, respectively.
    // Integers are not inherently signed or unsigned, their interpretation is
    // determined by individual operations.
    I32,
    #[allow(dead_code)]
    I64,
    // The types  and  classify 32 and 64 bit floating-point data, respectively.
    // They correspond to the respective binary floating-point representations,
    // also known as single and double precision, as defined by
    // the IEEE 754-2019 standard
    #[allow(dead_code)]
    F32,
    #[allow(dead_code)]
    F64,
}

/// Indices can be given either in raw numeric form or as symbolic identifiers
/// when bound by a respective construct. Such identifiers are looked up in
/// the suitable space of the identifier context _I_.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Index {
    Index(u32),
    Id(String),
}

// -- Use
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemoryUse(Index);

impl MemoryUse {
    pub fn new(index: Index) -> Self {
        Self(index)
    }

    pub fn index(&self) -> &Index {
        &self.0
    }
}

impl Default for MemoryUse {
    fn default() -> Self {
        Self(Index::Index(0))
    }
}

/// Wraps a construct with a referenced identifier.
///
/// Some constructs in WAT can be referenced by an identifier. This
/// struct wraps a construct with a referenced identifier.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Entity<T> {
    id: Option<String>,
    value: T,
}

impl<T> Entity<T> {
    /// Creates a new `Entity` containing the given value without
    /// an identifier.
    pub fn new(value: T) -> Self {
        Self { id: None, value }
    }

    /// Creates a new `Entity` containing the given value with
    /// an identifier.
    pub fn named(id: String, value: T) -> Self {
        Self {
            id: Some(id),
            value,
        }
    }

    pub fn id(&self) -> Option<&str> {
        self.id.as_deref()
    }

    pub fn get(&self) -> &T {
        &self.value
    }
}

impl<T: fmt::Debug> fmt::Debug for Entity<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut builder = f.debug_struct("Entity");

        if let Some(id) = self.id() {
            builder.field("id", &id);
        }

        builder.field("value", &self.value);
        builder.finish()
    }
}

/// Strings denote sequences of bytes that can represent both textual and
/// binary data. They are enclosed in quotation marks and may contain any
/// character other than ASCII control characters, quotation marks (`"`),
/// or backslash (`\`), except when expressed with an escape sequence.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StringData {
    String(String),
    Bytes(Box<[u8]>),
}

const HEX_CHARS: [char; 16] = [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
];

impl StringData {
    /// Writes a escaped string contents into buffer or streams.
    ///
    /// # Examples
    ///
    /// ```
    /// # use paty::gen::wasm::builder::StringData;
    /// let mut buffer = String::new();
    ///
    /// // string
    /// let string = StringData::String("\"hello\"\n".to_string());
    /// assert!(string.write_escape(&mut buffer).is_ok());
    /// assert_eq!(&buffer, "\\\"hello\\\"\\n");
    ///
    /// buffer.clear();
    /// let string = StringData::String("こんにちは".to_string());
    /// assert!(string.write_escape(&mut buffer).is_ok());
    /// assert_eq!(&buffer, "\\u{3053}\\u{3093}\\u{306b}\\u{3061}\\u{306f}");
    ///
    /// // bytes
    /// buffer.clear();
    /// let string = StringData::Bytes(Box::new([0, 1, 0xFF]));
    /// assert!(string.write_escape(&mut buffer).is_ok());
    /// assert_eq!(&buffer, "\\00\\01\\ff");
    /// ```
    pub fn write_escape<F: fmt::Write>(&self, f: &mut F) -> fmt::Result {
        match self {
            Self::String(s) => self.write_escape_string(f, s),
            Self::Bytes(b) => self.write_escape_bytes(f, b),
        }
    }

    fn write_escape_string<F: fmt::Write>(&self, f: &mut F, s: &str) -> fmt::Result {
        for c in s.escape_default() {
            f.write_char(c)?;
        }
        Ok(())
    }

    fn write_escape_bytes<F: fmt::Write>(&self, f: &mut F, bytes: &[u8]) -> fmt::Result {
        for &b in bytes {
            f.write_char('\\')?;
            let i = usize::try_from(b >> 4).unwrap();
            f.write_char(HEX_CHARS[i])?;
            let i = usize::try_from(0x0f & b).unwrap();
            f.write_char(HEX_CHARS[i])?;
        }
        Ok(())
    }
}

/// WebAssembly programs are organized into modules,
/// which are the unit of deployment, loading, and compilation.
///
/// https://webassembly.github.io/spec/core/syntax/modules.html
#[derive(Debug)]
pub struct Module {
    imports: Vec<Import>,
    exports: Vec<Export>,
    memory: Option<Entity<Memory>>,
    data_segments: Vec<Entity<DataSegment>>,
    functions: Vec<Entity<Function>>,
}

impl Default for Module {
    fn default() -> Self {
        Self::new()
    }
}

impl Module {
    pub fn new() -> Self {
        Self::with_memory(Entity::new(Memory::default()))
    }

    pub fn with_memory(memory: Entity<Memory>) -> Self {
        Self {
            memory: Some(memory),
            imports: vec![],
            exports: vec![],
            data_segments: vec![],
            functions: vec![],
        }
    }

    pub fn imports(&self) -> impl ExactSizeIterator<Item = &Import> {
        self.imports.iter()
    }
    pub fn exports(&self) -> impl ExactSizeIterator<Item = &Export> {
        self.exports.iter()
    }
    pub fn memory(&self) -> Option<&Entity<Memory>> {
        self.memory.as_ref()
    }
    pub fn data_segments(&self) -> impl ExactSizeIterator<Item = &Entity<DataSegment>> {
        self.data_segments.iter()
    }
    pub fn functions(&self) -> impl ExactSizeIterator<Item = &Entity<Function>> {
        self.functions.iter()
    }

    pub fn push_import(&mut self, import: Import) {
        self.imports.push(import);
    }
    pub fn push_export(&mut self, export: Export) {
        self.exports.push(export);
    }
    pub fn push_data_segment(&mut self, data_segment: Entity<DataSegment>) {
        self.data_segments.push(data_segment);
    }
    pub fn push_function(&mut self, function: Entity<Function>) {
        self.functions.push(function);
    }
}

/// The `imports` component of a module defines a set of imports that are
/// required for instantiation.
#[derive(Debug)]
pub struct Import {
    /// A `module` name.
    module: String,
    /// A name for an entity within that module.
    name: String,
    /// Each import is specified by a descriptor with a respective type that
    /// a definition provided during instantiation is required to match.
    desc: ImportDesc,
}

impl Import {
    pub fn new(module: String, name: String, desc: ImportDesc) -> Self {
        Self { module, name, desc }
    }

    pub fn module(&self) -> &str {
        self.module.as_str()
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn desc(&self) -> &ImportDesc {
        &self.desc
    }
}

#[derive(Debug)]
pub enum ImportDesc {
    Function(Entity<FunctionSignature>),
}

/// The `exports` component of a module defines a set of exports that become
/// accessible to the host environment once the module has been instantiated.
#[derive(Debug)]
pub struct Export {
    /// Each export is labeled by a unique name.
    name: String,
    /// Exportable definitions are functions, tables, memories, and globals,
    /// which are referenced through a respective descriptor.
    desc: ExportDesc,
}

impl Export {
    pub fn new(name: String, desc: ExportDesc) -> Self {
        Self { name, desc }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn desc(&self) -> &ExportDesc {
        &self.desc
    }
}

#[derive(Debug)]
pub enum ExportDesc {
    Function(Index),
    Memory(Index),
}

/// Memory types classify linear memories and their size range.
///
/// The limits constrain the minimum and optionally the maximum size of a memory.
/// The limits are given in units of page size.
#[derive(Debug, Default)]
pub struct Memory {
    limits: Limits,
}

impl Memory {
    /// Creates a new memory with 1 page memory.
    ///
    /// # Example
    ///
    /// ```
    /// # use paty::gen::wasm::builder::Memory;
    /// let mem = Memory::new();
    /// assert_eq!(mem.limits().min(), 1);
    /// assert_eq!(mem.limits().max(), None);
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new memory with the specified memory limits.
    ///
    /// # Example
    ///
    /// ```
    /// # use paty::gen::wasm::builder::{Memory, Limits};
    /// let mem = Memory::with_limits(Limits::with_max(2, 5));
    /// assert_eq!(mem.limits().min(), 2);
    /// assert_eq!(mem.limits().max(), Some(5));
    /// ```
    pub fn with_limits(limits: Limits) -> Self {
        Self { limits }
    }

    pub fn limits(&self) -> &Limits {
        &self.limits
    }
}

/// Limits classify the size range of resizeable storage associated with memory
/// types and table types.
///
/// If no maximum is given, the respective storage can
/// grow to any size.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Limits {
    min: u32,
    max: Option<u32>,
}

impl Limits {
    /// Creates a new limits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use paty::gen::wasm::builder::Limits;
    /// let limits = Limits::new(1);
    ///
    /// assert_eq!(limits.min(), 1);
    /// assert_eq!(limits.max(), None);
    /// ```
    pub fn new(min: u32) -> Self {
        Self { min, max: None }
    }

    /// Creates a new limits with the specified upper bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use paty::gen::wasm::builder::Limits;
    /// let limits = Limits::with_max(2, 5);
    ///
    /// assert_eq!(limits.min(), 2);
    /// assert_eq!(limits.max(), Some(5));
    /// ```
    pub fn with_max(min: u32, max: u32) -> Self {
        Self {
            min,
            max: Some(max),
        }
    }

    pub fn min(&self) -> u32 {
        self.min
    }

    pub fn max(&self) -> Option<u32> {
        self.max
    }
}

impl Default for Limits {
    fn default() -> Self {
        Self { min: 1, max: None }
    }
}

#[derive(Debug)]
pub struct FunctionSignature {
    params: Vec<Entity<Type>>,
    results: Vec<Type>,
}

impl FunctionSignature {
    pub fn new(params: Vec<Entity<Type>>, results: Vec<Type>) -> Self {
        Self { params, results }
    }

    pub fn params(&self) -> impl ExactSizeIterator<Item = &Entity<Type>> {
        self.params.iter()
    }

    pub fn results(&self) -> impl ExactSizeIterator<Item = &Type> {
        self.results.iter()
    }
}

/// Data segments allow for an optional memory index to identify the memory
/// to initialize. The data is written as a string, which may be split up into
/// a possibly empty sequence of individual string literals.
#[derive(Debug)]
pub struct DataSegment {
    memory: MemoryUse,
    offset: Vec<Instruction>,
    data: Vec<StringData>,
}

impl DataSegment {
    /// Creates a new data segment without memory use, defaulting to `0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use paty::gen::wasm::builder::{DataSegment, Index, Instruction, StringData, MemoryUse};
    ///
    /// let segment = DataSegment::new(
    ///     vec![Instruction::I32Const(8)],
    ///     vec![StringData::String("hello".to_string())]);
    ///
    /// assert_eq!(segment.memory(), &MemoryUse::new(Index::Index(0)));
    /// let mut offset = segment.offset();
    /// assert_eq!(offset.len(), 1);
    /// assert!(matches!(offset.next(), Some(Instruction::I32Const(8))));
    /// ```
    pub fn new(offset: Vec<Instruction>, data: Vec<StringData>) -> Self {
        Self::with_memory(MemoryUse::default(), offset, data)
    }

    pub fn with_memory(memory: MemoryUse, offset: Vec<Instruction>, data: Vec<StringData>) -> Self {
        Self {
            memory,
            offset,
            data,
        }
    }

    pub fn memory(&self) -> &MemoryUse {
        &self.memory
    }
    pub fn offset(&self) -> impl ExactSizeIterator<Item = &Instruction> {
        self.offset.iter()
    }
    pub fn data(&self) -> impl ExactSizeIterator<Item = &StringData> {
        self.data.iter()
    }
}

/// Function definitions can bind a symbolic function identifier, and local identifiers
/// for its parameters and locals.
///
/// # Examples
///
/// ```
/// # use paty::gen::wasm::builder::{Function, Entity, Type, Instruction};
/// let mut fun = Function::new();
///
/// assert_eq!(fun.signature().params().len(), 0);
/// assert_eq!(fun.signature().results().len(), 0);
///
/// fun.push_local(Entity::named("a".into(), Type::I32));
/// assert_eq!(fun.locals().len(), 1);
/// ```
#[derive(Debug)]
pub struct Function {
    signature: FunctionSignature,
    locals: Vec<Entity<Type>>,
    instructions: Vec<Instruction>,
}

impl Default for Function {
    fn default() -> Self {
        Self::new()
    }
}

impl Function {
    pub fn new() -> Self {
        Self::with_signature(FunctionSignature::new(
            Vec::with_capacity(0),
            Vec::with_capacity(0),
        ))
    }

    /// Creates a new function with the specified signature.
    ///
    /// # Examples
    ///
    /// ```
    /// # use paty::gen::wasm::builder::{Function, Entity, Type, Instruction, FunctionSignature};
    /// let signature = FunctionSignature::new(vec![Entity::named("x".into(), Type::I32)], vec![Type::I32]);
    /// let fun = Function::with_signature(signature);
    ///
    /// assert_eq!(fun.signature().params().len(), 1);
    /// assert_eq!(fun.signature().params().next(), Some(&Entity::named("x".into(), Type::I32)));
    /// assert_eq!(fun.signature().results().len(), 1);
    /// assert_eq!(fun.signature().results().next(), Some(&Type::I32));
    /// ```
    pub fn with_signature(signature: FunctionSignature) -> Self {
        Self {
            signature,
            locals: Vec::with_capacity(0),
            instructions: vec![],
        }
    }

    pub fn signature(&self) -> &FunctionSignature {
        &self.signature
    }
    pub fn locals(&self) -> impl ExactSizeIterator<Item = &Entity<Type>> {
        self.locals.iter()
    }
    pub fn instructions(&self) -> impl ExactSizeIterator<Item = &Instruction> {
        self.instructions.iter()
    }

    pub fn push_local(&mut self, local: Entity<Type>) {
        self.locals.push(local);
    }
    pub fn push_instruction(&mut self, inst: Instruction) {
        self.instructions.push(inst);
    }
}

/// WebAssembly code consists of sequences of instructions. Its computational model is
/// based on a stack machine in that instructions manipulate values on an implicit
/// operand stack, consuming (popping) argument values and producing or
/// returning (pushing) result values.
///
/// In addition to dynamic operands from the stack, some instructions also have static
/// immediate arguments, typically indices or type annotations, which are part of
/// the instruction itself.
///
/// Some instructions are structured in that they bracket nested sequences of instructions.
#[derive(Debug, Clone)]
pub struct Instruction {
    kind: InstructionKind,
    operands: Vec<Instruction>,
}

impl Instruction {
    pub fn new(kind: InstructionKind, operands: Vec<Instruction>) -> Self {
        Self { kind, operands }
    }

    pub fn kind(&self) -> &InstructionKind {
        &self.kind
    }
    pub fn operands(&self) -> impl ExactSizeIterator<Item = &Instruction> {
        self.operands.iter()
    }
}

impl Instruction {
    pub fn i32_const(n: u32) -> Self {
        Self::new(InstructionKind::I32Const(n), vec![])
    }
    pub fn i64_const(n: u64) -> Self {
        Self::new(InstructionKind::I64Const(n), vec![])
    }
    pub fn i32_store(operands: Vec<Instruction>) -> Self {
        Self::new(InstructionKind::I32Store(MemArg::default()), operands)
    }
    pub fn i64_store(operands: Vec<Instruction>) -> Self {
        Self::new(InstructionKind::I64Store(MemArg::default()), operands)
    }
    pub fn call(index: Index, operands: Vec<Instruction>) -> Self {
        Self::new(InstructionKind::Call(index), operands)
    }
    pub fn drop() -> Self {
        Self::new(InstructionKind::Drop, vec![])
    }
}

#[derive(Debug, Clone)]
pub enum InstructionKind {
    /// `i32.const {inn}`
    I32Const(u32),
    /// `i64.const {inn}`
    I64Const(u64),
    /// `i32.store [offset=N] [align=M]`
    I32Store(MemArg),
    /// `i64.store [offset=N] [align=M]`
    I64Store(MemArg),
    /// `call x:funcidx`
    Call(Index),
    /// `drop`
    Drop,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct MemArg {
    offset: Option<u32>,
    align: Option<u32>,
}

impl MemArg {
    pub fn new(offset: Option<u32>, align: Option<u32>) -> Self {
        Self { offset, align }
    }

    pub fn offset(&self) -> Option<u32> {
        self.offset
    }
    pub fn align(&self) -> Option<u32> {
        self.align
    }
}

pub trait Visitor {
    fn enter_module(&mut self, module: &Entity<Module>);
    fn exit_module(&mut self, module: &Entity<Module>);

    fn enter_import(&mut self, import: &Import);
    fn exit_import(&mut self, import: &Import);

    fn enter_export(&mut self, export: &Export);
    fn exit_export(&mut self, export: &Export);

    fn enter_memory(&mut self, memory: &Entity<Memory>);
    fn exit_memory(&mut self, memory: &Entity<Memory>);

    fn enter_data_segment(&mut self, data_segment: &Entity<DataSegment>);
    fn exit_data_segment(&mut self, data_segment: &Entity<DataSegment>);

    fn enter_function(&mut self, function: &Entity<Function>);
    fn exit_function(&mut self, function: &Entity<Function>);
}

fn walk(visitor: &mut dyn Visitor, module: &Entity<Module>) {
    visitor.enter_module(module);

    // imports
    for import in module.get().imports() {
        visitor.enter_import(import);
        visitor.exit_import(import);
    }

    // exports
    for export in module.get().exports() {
        visitor.enter_export(export);
        visitor.exit_export(export);
    }

    // memory
    if let Some(memory) = module.get().memory() {
        visitor.enter_memory(memory);
        visitor.exit_memory(memory);
    }

    // data segments
    for data_segment in module.get().data_segments() {
        visitor.enter_data_segment(data_segment);
        visitor.exit_data_segment(data_segment);
    }

    // functions
    for function in module.get().functions() {
        visitor.enter_function(function);
        visitor.exit_function(function);
    }

    visitor.exit_module(module);
}

#[derive(Debug, Default)]
pub struct WatBuilder {
    buffer: String,
}

impl WatBuilder {
    pub fn new() -> Self {
        Self {
            buffer: String::new(),
        }
    }

    pub fn emit(&mut self, module: &Entity<Module>) -> String {
        self.buffer.clear();

        walk(self, module);
        std::mem::take(&mut self.buffer)
    }

    fn emit_index(&mut self, index: &Index) {
        match index {
            &Index::Index(i) => {
                self.buffer.push(' ');
                self.buffer.push_str(&i.to_string());
            }
            Index::Id(id) => self.emit_id(id),
        }
    }
    fn emit_id(&mut self, id: &str) {
        self.buffer.push(' ');
        self.buffer.push('$');
        self.buffer.push_str(id);
    }
    fn emit_str(&mut self, s: &str) {
        self.buffer.push(' ');
        self.buffer.push('"');
        for c in s.escape_default() {
            self.buffer.push(c);
        }
        self.buffer.push('"');
    }
    fn emit_string_data(&mut self, s: &StringData) {
        self.buffer.push(' ');
        self.buffer.push('"');
        s.write_escape(&mut self.buffer).expect("unreachable");
        self.buffer.push('"');
    }
    fn emit_type(&mut self, ty: &Type) {
        self.buffer.push(' ');
        self.buffer.push_str(match ty {
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::F32 => "f32",
            Type::F64 => "f64",
        });
    }
    fn emit_limits(&mut self, limits: &Limits) {
        self.buffer.push(' ');
        self.buffer.push_str(&limits.min().to_string());

        if let Some(max) = limits.max() {
            self.buffer.push(' ');
            self.buffer.push_str(&max.to_string());
        }
    }
    fn emit_function_signature(&mut self, signature: &FunctionSignature) {
        self.buffer.push(' ');
        for param in signature.params() {
            self.buffer.push('(');
            self.buffer.push_str("param");
            if let Some(name) = param.id() {
                self.emit_id(name);
            }
            self.emit_type(param.get());
            self.buffer.push(')');
        }

        for ty in signature.results() {
            self.buffer.push('(');
            self.buffer.push_str("result");
            self.emit_type(ty);
            self.buffer.push(')');
        }
    }
    fn emit_import_desc_function(&mut self, fun: &Entity<FunctionSignature>) {
        self.buffer.push('(');
        self.buffer.push_str("func");

        if let Some(name) = fun.id() {
            self.emit_id(name);
        }
        self.emit_function_signature(fun.get());
        self.buffer.push(')');
    }
    fn emit_mem_arg(&mut self, mem: &MemArg) {
        if let Some(offset) = mem.offset() {
            self.buffer.push(' ');
            self.buffer.push_str("offset=");
            self.buffer.push_str(&offset.to_string());
        }
        if let Some(align) = mem.align() {
            self.buffer.push(' ');
            self.buffer.push_str("align=");
            self.buffer.push_str(&align.to_string());
        }
    }
    fn emit_inst(&mut self, inst: &Instruction) {
        self.buffer.push('(');
        match inst.kind() {
            InstructionKind::I32Const(n) => {
                self.buffer.push_str("i32.const");
                self.buffer.push(' ');
                self.buffer.push_str(&n.to_string());
            }
            InstructionKind::I64Const(n) => {
                self.buffer.push_str("i64.const");
                self.buffer.push(' ');
                self.buffer.push_str(&n.to_string());
            }
            InstructionKind::I32Store(mem) => {
                self.buffer.push_str("i32.store");
                self.emit_mem_arg(mem);
            }
            InstructionKind::I64Store(mem) => {
                self.buffer.push_str("i64.store");
                self.emit_mem_arg(mem);
            }
            InstructionKind::Call(index) => {
                self.buffer.push_str("call");
                self.emit_index(index);
            }
            InstructionKind::Drop => {
                self.buffer.push_str("drop");
            }
        }
        for operand in inst.operands() {
            self.emit_inst(operand);
        }

        self.buffer.push(')');
    }
}

impl Visitor for WatBuilder {
    fn enter_module(&mut self, module: &Entity<Module>) {
        self.buffer.push('(');
        self.buffer.push_str("module");

        if let Some(name) = module.id() {
            self.emit_id(name);
        }
    }
    fn exit_module(&mut self, _module: &Entity<Module>) {
        self.buffer.push(')');
    }

    fn enter_import(&mut self, import: &Import) {
        self.buffer.push('(');
        self.buffer.push_str("import");

        self.emit_str(import.module());
        self.emit_str(import.name());
        self.buffer.push(' ');

        match import.desc() {
            ImportDesc::Function(fun) => self.emit_import_desc_function(fun),
        }
    }
    fn exit_import(&mut self, _import: &Import) {
        self.buffer.push(')');
    }

    fn enter_export(&mut self, export: &Export) {
        self.buffer.push('(');
        self.buffer.push_str("export");

        self.emit_str(export.name());
        self.buffer.push(' ');

        self.buffer.push('(');
        match export.desc() {
            ExportDesc::Function(idx) => {
                self.buffer.push_str("func");
                self.emit_index(idx);
            }
            ExportDesc::Memory(idx) => {
                self.buffer.push_str("memory");
                self.emit_index(idx);
            }
        }
        self.buffer.push(')');
    }
    fn exit_export(&mut self, _export: &Export) {
        self.buffer.push(')');
    }

    fn enter_memory(&mut self, memory: &Entity<Memory>) {
        self.buffer.push('(');
        self.buffer.push_str("memory");

        if let Some(name) = memory.id() {
            self.emit_id(name);
        }

        self.emit_limits(memory.get().limits());
    }
    fn exit_memory(&mut self, _memory: &Entity<Memory>) {
        self.buffer.push(')');
    }

    fn enter_data_segment(&mut self, data_segment: &Entity<DataSegment>) {
        self.buffer.push('(');
        self.buffer.push_str("data");

        // id
        if let Some(name) = data_segment.id() {
            self.emit_id(name);
        }

        // memuse
        self.buffer.push(' ');
        self.buffer.push('(');
        self.buffer.push_str("memory");
        self.emit_index(data_segment.get().memory().index());
        self.buffer.push(')');

        // offset
        self.buffer.push(' ');
        self.buffer.push('(');
        self.buffer.push_str("offset");
        self.buffer.push(' ');
        for inst in data_segment.get().offset() {
            self.emit_inst(inst);
        }
        self.buffer.push(')');

        // data
        for s in data_segment.get().data() {
            self.emit_string_data(s);
        }
    }
    fn exit_data_segment(&mut self, _data_segment: &Entity<DataSegment>) {
        self.buffer.push(')');
    }

    fn enter_function(&mut self, fun: &Entity<Function>) {
        self.buffer.push('(');
        self.buffer.push_str("func");

        // id
        if let Some(name) = fun.id() {
            self.emit_id(name);
        }

        self.emit_function_signature(fun.get().signature());

        // locals
        for local in fun.get().locals() {
            self.buffer.push('(');
            self.buffer.push_str("local");
            if let Some(name) = local.id() {
                self.emit_id(name);
            }
            self.emit_type(local.get());
            self.buffer.push(')');
        }

        // instructions
        for inst in fun.get().instructions() {
            self.emit_inst(inst);
        }
    }
    fn exit_function(&mut self, _function: &Entity<Function>) {
        self.buffer.push(')');
    }
}
