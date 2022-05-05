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

impl From<&str> for Index {
    fn from(s: &str) -> Self {
        Self::Id(s.to_string())
    }
}

impl From<String> for Index {
    fn from(s: String) -> Self {
        Self::Id(s)
    }
}

impl From<u32> for Index {
    fn from(n: u32) -> Self {
        Self::Index(n)
    }
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
    pub fn named<I: Into<String>>(id: I, value: T) -> Self {
        Self {
            id: Some(id.into()),
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
    Bytes(Vec<u8>),
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
    globals: Vec<Entity<Global>>,
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
            globals: vec![],
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
    pub fn globals(&self) -> impl ExactSizeIterator<Item = &Entity<Global>> {
        self.globals.iter()
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
    pub fn push_global(&mut self, global: Entity<Global>) {
        self.globals.push(global);
    }
    pub fn push_function(&mut self, function: Entity<Function>) {
        self.functions.push(function);
    }
    pub fn prepend_function(&mut self, function: Entity<Function>) {
        self.functions.insert(0, function);
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

/// Limits classify the size range of resizable storage associated with memory
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    ///     vec![Instruction::i32_const(8)],
    ///     vec![StringData::String("hello".to_string())]);
    ///
    /// assert_eq!(segment.memory(), &MemoryUse::new(Index::Index(0)));
    /// let mut offset = segment.offset();
    /// assert_eq!(offset.len(), 1);
    /// let next_inst = offset.next();
    /// assert!(next_inst.is_some());
    /// assert_eq!(next_inst.unwrap(), &Instruction::i32_const(8));
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

/// The _globals_ component of a module defines a vector of global variables (or
/// globals for short):
///
/// Each global stores a single value of the given global type. Its type also specifies
/// whether a global is immutable or mutable. Moreover, each global is initialized with
/// an value given by a constant initializer expression.
#[derive(Debug, Clone)]
pub struct Global {
    mutable: bool,
    ty: Type,
    init: Vec<Instruction>,
}

impl Global {
    pub fn new(mutable: bool, ty: Type, init: Vec<Instruction>) -> Self {
        Self { mutable, ty, init }
    }

    pub fn is_mutable(&self) -> bool {
        self.mutable
    }
    pub fn ty(&self) -> &Type {
        &self.ty
    }
    pub fn initializer(&self) -> impl ExactSizeIterator<Item = &Instruction> {
        self.init.iter()
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
/// fun.push_local(Entity::named("a", Type::I32));
/// assert_eq!(fun.locals().len(), 1);
/// ```
#[derive(Debug)]
pub struct Function {
    signature: FunctionSignature,
    locals: Vec<Entity<Type>>,
    body: Instructions,
    // Abbreviations: `(func id? (export name) ...)` can be applied repeatedly.
    exports: Vec<String>,
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
    /// let signature = FunctionSignature::new(vec![Entity::named("x", Type::I32)], vec![Type::I32]);
    /// let fun = Function::with_signature(signature);
    ///
    /// assert_eq!(fun.signature().params().len(), 1);
    /// assert_eq!(fun.signature().params().next(), Some(&Entity::named("x", Type::I32)));
    /// assert_eq!(fun.signature().results().len(), 1);
    /// assert_eq!(fun.signature().results().next(), Some(&Type::I32));
    /// ```
    pub fn with_signature(signature: FunctionSignature) -> Self {
        Self {
            signature,
            locals: vec![],
            body: Instructions::new(),
            exports: vec![],
        }
    }

    pub fn signature(&self) -> &FunctionSignature {
        &self.signature
    }
    pub fn body(&self) -> &Instructions {
        &self.body
    }
    pub fn body_mut(&mut self) -> &mut Instructions {
        &mut self.body
    }

    pub fn locals(&self) -> impl ExactSizeIterator<Item = &Entity<Type>> {
        self.locals.iter()
    }
    pub fn push_local(&mut self, local: Entity<Type>) {
        self.locals.push(local);
    }

    pub fn exports(&self) -> impl ExactSizeIterator<Item = &str> {
        self.exports.iter().map(AsRef::as_ref)
    }
    pub fn push_export(&mut self, name: String) {
        self.exports.push(name);
    }

    /// Adds a new temporary variable with the given type and
    /// returns its index.
    ///
    /// # Examples
    ///
    /// ```
    /// # use paty::gen::wasm::builder::{Function, Entity, Type, Instruction, FunctionSignature};
    /// let mut fun = Function::new();
    /// let tmp1 = fun.push_tmp(Type::I32);
    /// let tmp2 = fun.push_tmp(Type::I32);
    ///
    /// assert_eq!(fun.locals().len(), 2);
    /// assert_ne!(tmp1, tmp2);
    /// ```
    pub fn push_tmp(&mut self, ty: Type) -> Index {
        // The index space for locals is only accessible inside a function and
        // includes the parameters of that function, which precede the local variables.
        let idx = self.signature.params().len() + self.locals.len();

        self.push_local(Entity::new(ty));
        Index::Index(u32::try_from(idx).unwrap())
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
#[derive(Debug, Clone, PartialEq, Eq)]
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

    /// Returns `true` if the instruction has operands.
    pub fn has_operands(&self) -> bool {
        !self.operands.is_empty()
    }
}

impl Instruction {
    pub fn i32_const(n: u32) -> Self {
        Self::new(InstructionKind::I32Const(n), vec![])
    }
    pub fn i64_const(n: u64) -> Self {
        Self::new(InstructionKind::I64Const(n), vec![])
    }
    pub fn i32_store(dst: Instruction, src: Instruction) -> Self {
        Self::i32_store_m(MemArg::default(), dst, src)
    }
    pub fn i32_store8(dst: Instruction, src: Instruction) -> Self {
        Self::i32_store8_m(MemArg::default(), dst, src)
    }
    pub fn i32_store_m(mem: MemArg, dst: Instruction, src: Instruction) -> Self {
        Self::new(InstructionKind::I32Store(mem), vec![dst, src])
    }
    pub fn i32_store8_m(mem: MemArg, dst: Instruction, src: Instruction) -> Self {
        Self::new(InstructionKind::I32Store8(mem), vec![dst, src])
    }
    pub fn i64_store(dst: Instruction, src: Instruction) -> Self {
        Self::new(InstructionKind::I64Store(MemArg::default()), vec![dst, src])
    }
    pub fn i32_load(src: Instruction) -> Self {
        Self::i32_load_m(MemArg::default(), src)
    }
    pub fn i32_load8_s(src: Instruction) -> Self {
        Self::i32_load8_s_m(MemArg::default(), src)
    }
    pub fn i32_load8_u(src: Instruction) -> Self {
        Self::i32_load8_u_m(MemArg::default(), src)
    }
    pub fn i32_load_m(mem: MemArg, src: Instruction) -> Self {
        Self::new(InstructionKind::I32Load(mem), vec![src])
    }
    pub fn i32_load8_s_m(mem: MemArg, src: Instruction) -> Self {
        Self::new(InstructionKind::I32Load8S(mem), vec![src])
    }
    pub fn i32_load8_u_m(mem: MemArg, src: Instruction) -> Self {
        Self::new(InstructionKind::I32Load8U(mem), vec![src])
    }
    pub fn i64_load(src: Instruction) -> Self {
        Self::new(InstructionKind::I64Load(MemArg::default()), vec![src])
    }
    pub fn i32_add(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32Add, vec![lhs, rhs])
    }
    pub fn i32_sub(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32Sub, vec![lhs, rhs])
    }
    pub fn i32_mul(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32Mul, vec![lhs, rhs])
    }
    pub fn i32_div_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32DivU, vec![lhs, rhs])
    }
    pub fn i32_div_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32DivS, vec![lhs, rhs])
    }
    pub fn i32_rem_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32RemU, vec![lhs, rhs])
    }
    pub fn i32_rem_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32RemS, vec![lhs, rhs])
    }
    pub fn i32_and(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32And, vec![lhs, rhs])
    }
    pub fn i32_or(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32Or, vec![lhs, rhs])
    }
    pub fn i32_xor(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32Xor, vec![lhs, rhs])
    }
    pub fn i32_shl(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32ShiLeft, vec![lhs, rhs])
    }
    pub fn i32_shr_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32ShiftRightU, vec![lhs, rhs])
    }
    pub fn i32_shr_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32ShiftRightS, vec![lhs, rhs])
    }
    pub fn i32_clz(operand: Instruction) -> Self {
        Self::new(InstructionKind::I32Clz, vec![operand])
    }
    pub fn i32_ctz(operand: Instruction) -> Self {
        Self::new(InstructionKind::I32Ctz, vec![operand])
    }
    pub fn i32_popcnt(operand: Instruction) -> Self {
        Self::new(InstructionKind::I32PopCnt, vec![operand])
    }
    pub fn i32_eqz(operand: Instruction) -> Self {
        Self::new(InstructionKind::I32Eqz, vec![operand])
    }
    pub fn i32_eq(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32Eq, vec![lhs, rhs])
    }
    pub fn i32_ne(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32Ne, vec![lhs, rhs])
    }
    pub fn i32_lt_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32LtU, vec![lhs, rhs])
    }
    pub fn i32_lt_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32LtS, vec![lhs, rhs])
    }
    pub fn i32_gt_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32GtU, vec![lhs, rhs])
    }
    pub fn i32_gt_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32GtS, vec![lhs, rhs])
    }
    pub fn i32_le_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32LeU, vec![lhs, rhs])
    }
    pub fn i32_le_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32LeS, vec![lhs, rhs])
    }
    pub fn i32_ge_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32GeU, vec![lhs, rhs])
    }
    pub fn i32_ge_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I32GeS, vec![lhs, rhs])
    }
    pub fn i32_add_() -> Self {
        Self::new(InstructionKind::I32Add, vec![])
    }
    pub fn i32_sub_() -> Self {
        Self::new(InstructionKind::I32Sub, vec![])
    }
    pub fn i32_mul_() -> Self {
        Self::new(InstructionKind::I32Mul, vec![])
    }
    pub fn i32_div_u_() -> Self {
        Self::new(InstructionKind::I32DivU, vec![])
    }
    pub fn i32_div_s_() -> Self {
        Self::new(InstructionKind::I32DivS, vec![])
    }
    pub fn i32_rem_u_() -> Self {
        Self::new(InstructionKind::I32RemU, vec![])
    }
    pub fn i32_rem_s_() -> Self {
        Self::new(InstructionKind::I32RemS, vec![])
    }
    pub fn i32_and_() -> Self {
        Self::new(InstructionKind::I32And, vec![])
    }
    pub fn i32_or_() -> Self {
        Self::new(InstructionKind::I32Or, vec![])
    }
    pub fn i32_xor_() -> Self {
        Self::new(InstructionKind::I32Xor, vec![])
    }
    pub fn i32_shl_() -> Self {
        Self::new(InstructionKind::I32ShiLeft, vec![])
    }
    pub fn i32_shr_u_() -> Self {
        Self::new(InstructionKind::I32ShiftRightU, vec![])
    }
    pub fn i32_shr_s_() -> Self {
        Self::new(InstructionKind::I32ShiftRightS, vec![])
    }
    pub fn i32_clz_() -> Self {
        Self::new(InstructionKind::I32Clz, vec![])
    }
    pub fn i32_ctz_() -> Self {
        Self::new(InstructionKind::I32Ctz, vec![])
    }
    pub fn i32_popcnt_() -> Self {
        Self::new(InstructionKind::I32PopCnt, vec![])
    }
    pub fn i32_eqz_() -> Self {
        Self::new(InstructionKind::I32Eqz, vec![])
    }
    pub fn i32_eq_() -> Self {
        Self::new(InstructionKind::I32Eq, vec![])
    }
    pub fn i32_ne_() -> Self {
        Self::new(InstructionKind::I32Ne, vec![])
    }
    pub fn i32_lt_u_() -> Self {
        Self::new(InstructionKind::I32LtU, vec![])
    }
    pub fn i32_lt_s_() -> Self {
        Self::new(InstructionKind::I32LtS, vec![])
    }
    pub fn i32_gt_u_() -> Self {
        Self::new(InstructionKind::I32GtU, vec![])
    }
    pub fn i32_gt_s_() -> Self {
        Self::new(InstructionKind::I32GtS, vec![])
    }
    pub fn i32_le_u_() -> Self {
        Self::new(InstructionKind::I32LeU, vec![])
    }
    pub fn i32_le_s_() -> Self {
        Self::new(InstructionKind::I32LeS, vec![])
    }
    pub fn i32_ge_u_() -> Self {
        Self::new(InstructionKind::I32GeU, vec![])
    }
    pub fn i32_ge_s_() -> Self {
        Self::new(InstructionKind::I32GeS, vec![])
    }
    pub fn i64_add(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64Add, vec![lhs, rhs])
    }
    pub fn i64_sub(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64Sub, vec![lhs, rhs])
    }
    pub fn i64_mul(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64Mul, vec![lhs, rhs])
    }
    pub fn i64_div_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64DivU, vec![lhs, rhs])
    }
    pub fn i64_div_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64DivS, vec![lhs, rhs])
    }
    pub fn i64_rem_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64RemU, vec![lhs, rhs])
    }
    pub fn i64_rem_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64RemS, vec![lhs, rhs])
    }
    pub fn i64_and(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64And, vec![lhs, rhs])
    }
    pub fn i64_or(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64Or, vec![lhs, rhs])
    }
    pub fn i64_xor(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64Xor, vec![lhs, rhs])
    }
    pub fn i64_shl(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64ShiLeft, vec![lhs, rhs])
    }
    pub fn i64_shr_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64ShiftRightU, vec![lhs, rhs])
    }
    pub fn i64_shr_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64ShiftRightS, vec![lhs, rhs])
    }
    pub fn i64_clz(operand: Instruction) -> Self {
        Self::new(InstructionKind::I64Clz, vec![operand])
    }
    pub fn i64_ctz(operand: Instruction) -> Self {
        Self::new(InstructionKind::I64Ctz, vec![operand])
    }
    pub fn i64_popcnt(operand: Instruction) -> Self {
        Self::new(InstructionKind::I64PopCnt, vec![operand])
    }
    pub fn i64_eqz(operand: Instruction) -> Self {
        Self::new(InstructionKind::I64Eqz, vec![operand])
    }
    pub fn i64_eq(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64Eq, vec![lhs, rhs])
    }
    pub fn i64_ne(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64Ne, vec![lhs, rhs])
    }
    pub fn i64_lt_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64LtU, vec![lhs, rhs])
    }
    pub fn i64_lt_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64LtS, vec![lhs, rhs])
    }
    pub fn i64_gt_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64GtU, vec![lhs, rhs])
    }
    pub fn i64_gt_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64GtS, vec![lhs, rhs])
    }
    pub fn i64_le_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64LeU, vec![lhs, rhs])
    }
    pub fn i64_le_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64LeS, vec![lhs, rhs])
    }
    pub fn i64_ge_u(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64GeU, vec![lhs, rhs])
    }
    pub fn i64_ge_s(lhs: Instruction, rhs: Instruction) -> Self {
        Self::new(InstructionKind::I64GeS, vec![lhs, rhs])
    }
    pub fn i64_add_() -> Self {
        Self::new(InstructionKind::I64Add, vec![])
    }
    pub fn i64_sub_() -> Self {
        Self::new(InstructionKind::I64Sub, vec![])
    }
    pub fn i64_mul_() -> Self {
        Self::new(InstructionKind::I64Mul, vec![])
    }
    pub fn i64_div_u_() -> Self {
        Self::new(InstructionKind::I64DivU, vec![])
    }
    pub fn i64_div_s_() -> Self {
        Self::new(InstructionKind::I64DivS, vec![])
    }
    pub fn i64_rem_u_() -> Self {
        Self::new(InstructionKind::I64RemU, vec![])
    }
    pub fn i64_rem_s_() -> Self {
        Self::new(InstructionKind::I64RemS, vec![])
    }
    pub fn i64_and_() -> Self {
        Self::new(InstructionKind::I64And, vec![])
    }
    pub fn i64_or_() -> Self {
        Self::new(InstructionKind::I64Or, vec![])
    }
    pub fn i64_xor_() -> Self {
        Self::new(InstructionKind::I64Xor, vec![])
    }
    pub fn i64_shl_() -> Self {
        Self::new(InstructionKind::I64ShiLeft, vec![])
    }
    pub fn i64_shr_u_() -> Self {
        Self::new(InstructionKind::I64ShiftRightU, vec![])
    }
    pub fn i64_shr_s_() -> Self {
        Self::new(InstructionKind::I64ShiftRightS, vec![])
    }
    pub fn i64_eq_() -> Self {
        Self::new(InstructionKind::I64Eq, vec![])
    }
    pub fn i64_ne_() -> Self {
        Self::new(InstructionKind::I64Ne, vec![])
    }
    pub fn i64_lt_u_() -> Self {
        Self::new(InstructionKind::I64LtU, vec![])
    }
    pub fn i64_lt_s_() -> Self {
        Self::new(InstructionKind::I64LtS, vec![])
    }
    pub fn i64_gt_u_() -> Self {
        Self::new(InstructionKind::I64GtU, vec![])
    }
    pub fn i64_gt_s_() -> Self {
        Self::new(InstructionKind::I64GtS, vec![])
    }
    pub fn i64_le_u_() -> Self {
        Self::new(InstructionKind::I64LeU, vec![])
    }
    pub fn i64_le_s_() -> Self {
        Self::new(InstructionKind::I64LeS, vec![])
    }
    pub fn i64_ge_u_() -> Self {
        Self::new(InstructionKind::I64GeU, vec![])
    }
    pub fn i64_ge_s_() -> Self {
        Self::new(InstructionKind::I64GeS, vec![])
    }
    // conversions
    pub fn i64_extend_i32_s(operand: Instruction) -> Self {
        Self::new(InstructionKind::I64ExtendI32S, vec![operand])
    }
    pub fn i64_extend_i32_u(operand: Instruction) -> Self {
        Self::new(InstructionKind::I64ExtendI32U, vec![operand])
    }
    pub fn i32_wrap_i64(operand: Instruction) -> Self {
        Self::new(InstructionKind::I32WrapI64, vec![operand])
    }
    // locals
    pub fn local_get<T: Into<Index>>(index: T) -> Self {
        Self::new(InstructionKind::LocalGet(index.into()), vec![])
    }
    pub fn local_set<T: Into<Index>>(index: T, value: Instruction) -> Self {
        Self::new(InstructionKind::LocalSet(index.into()), vec![value])
    }
    pub fn local_set_<T: Into<Index>>(index: T) -> Self {
        Self::new(InstructionKind::LocalSet(index.into()), vec![])
    }
    pub fn local_tee<T: Into<Index>>(index: T, value: Instruction) -> Self {
        Self::new(InstructionKind::LocalTee(index.into()), vec![value])
    }
    pub fn global_get<T: Into<Index>>(index: T) -> Self {
        Self::new(InstructionKind::GlobalGet(index.into()), vec![])
    }
    pub fn global_set<T: Into<Index>>(index: T, value: Instruction) -> Self {
        Self::new(InstructionKind::GlobalSet(index.into()), vec![value])
    }
    pub fn call<T: Into<Index>>(index: T, operands: Vec<Instruction>) -> Self {
        Self::new(InstructionKind::Call(index.into()), operands)
    }
    pub fn drop() -> Self {
        Self::new(InstructionKind::Drop, vec![])
    }
    pub fn select(
        then_value: Instruction,
        else_value: Instruction,
        cond_value: Instruction,
    ) -> Self {
        Self::new(
            InstructionKind::Select,
            vec![then_value, else_value, cond_value],
        )
    }
    pub fn nop() -> Self {
        Self::new(InstructionKind::Nop, vec![])
    }
    pub fn unreachable() -> Self {
        Self::new(InstructionKind::Unreachable, vec![])
    }
    pub fn block(wasm_block: BlockInstruction) -> Self {
        Self::new(InstructionKind::Block(wasm_block), vec![])
    }
    pub fn r#loop(wasm_loop: LoopInstruction) -> Self {
        Self::new(InstructionKind::Loop(wasm_loop), vec![])
    }
    pub fn r#if(wasm_if: IfInstruction) -> Self {
        Self::new(InstructionKind::If(wasm_if), vec![])
    }
    pub fn br(label_idx: u32) -> Self {
        Self::new(InstructionKind::Br(label_idx), vec![])
    }
    pub fn br_if(label_idx: u32, cond: Instruction) -> Self {
        Self::new(InstructionKind::BrIf(label_idx), vec![cond])
    }
    pub fn br_if_(label_idx: u32) -> Self {
        Self::new(InstructionKind::BrIf(label_idx), vec![])
    }
    pub fn r#return() -> Self {
        Self::new(InstructionKind::Return, vec![])
    }

    // ext: bulk-memory
    pub fn memory_copy(n: Instruction, src: Instruction, dst: Instruction) -> Self {
        Self::new(InstructionKind::MemoryCopy, vec![n, src, dst])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstructionKind {
    // const
    I32Const(u32),
    I64Const(u64),
    // integer binary operators
    I32Add,
    I32Sub,
    I32Mul,
    I32DivU,
    I32DivS,
    I32RemU,
    I32RemS,
    I32And,
    I32Or,
    I32Xor,
    I32ShiLeft,
    I32ShiftRightU,
    I32ShiftRightS,
    I32RotateLeft,
    I32RotateRight,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivU,
    I64DivS,
    I64RemU,
    I64RemS,
    I64And,
    I64Or,
    I64Xor,
    I64ShiLeft,
    I64ShiftRightU,
    I64ShiftRightS,
    I64RotateLeft,
    I64RotateRight,
    // integer unary operators
    I32Clz,
    I32Ctz,
    I32PopCnt,
    I64Clz,
    I64Ctz,
    I64PopCnt,
    // integer test and relations
    I32Eqz,
    I32Eq,
    I32Ne,
    I32LtU,
    I32LtS,
    I32GtU,
    I32GtS,
    I32LeU,
    I32LeS,
    I32GeU,
    I32GeS,
    I64Eqz,
    I64Eq,
    I64Ne,
    I64LtU,
    I64LtS,
    I64GtU,
    I64GtS,
    I64LeU,
    I64LeS,
    I64GeU,
    I64GeS,
    // conversions
    I64ExtendI32S, // [i32] -> [i64]
    I64ExtendI32U, // [i32] -> [i64]
    I32WrapI64,    // [i64] -> [i32]
    // memory instructions
    I32Store(MemArg),
    I32Store8(MemArg),
    I64Store(MemArg),
    I32Load(MemArg),
    I32Load8S(MemArg),
    I32Load8U(MemArg),
    I64Load(MemArg),
    // local variables
    LocalGet(Index),
    LocalSet(Index),
    LocalTee(Index),
    // globals
    GlobalGet(Index),
    GlobalSet(Index),
    Call(Index),
    // parametric instructions
    Drop,
    // The `select` instruction selects one of its first two operands based
    // on whether its third operand is zero or not.
    Select,
    // control instructions
    Nop,
    Unreachable,
    Block(BlockInstruction),
    If(IfInstruction),
    Loop(LoopInstruction),
    Br(u32),
    BrIf(u32),
    Return,
    // Ext: bulk-memory
    MemoryCopy,
}

/// Instruction buffer and builder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instructions {
    instructions: Vec<Instruction>,
}

impl Default for Instructions {
    fn default() -> Self {
        Self::new()
    }
}

impl Instructions {
    pub fn i32_const(&mut self, n: u32) -> &mut Self {
        self.instructions.push(Instruction::i32_const(n));
        self
    }
    pub fn i64_const(&mut self, n: u64) -> &mut Self {
        self.instructions.push(Instruction::i64_const(n));
        self
    }
    pub fn i32_store(&mut self, dst: Instruction, src: Instruction) -> &mut Self {
        self.i32_store_m(MemArg::default(), dst, src)
    }
    pub fn i32_store8(&mut self, dst: Instruction, src: Instruction) -> &mut Self {
        self.i32_store8_m(MemArg::default(), dst, src)
    }
    pub fn i32_store_m(&mut self, mem: MemArg, dst: Instruction, src: Instruction) -> &mut Self {
        self.instructions
            .push(Instruction::i32_store_m(mem, dst, src));
        self
    }
    pub fn i32_store8_m(&mut self, mem: MemArg, dst: Instruction, src: Instruction) -> &mut Self {
        self.instructions
            .push(Instruction::i32_store8_m(mem, dst, src));
        self
    }
    pub fn i64_store(&mut self, dst: Instruction, src: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_store(dst, src));
        self
    }
    pub fn i32_load(&mut self, src: Instruction) -> &mut Self {
        self.i32_load_m(MemArg::default(), src)
    }
    pub fn i32_load8_s(&mut self, src: Instruction) -> &mut Self {
        self.i32_load8_s_m(MemArg::default(), src)
    }
    pub fn i32_load8_u(&mut self, src: Instruction) -> &mut Self {
        self.i32_load8_u_m(MemArg::default(), src)
    }
    pub fn i32_load_m(&mut self, mem: MemArg, src: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_load_m(mem, src));
        self
    }
    pub fn i32_load8_s_m(&mut self, mem: MemArg, src: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_load8_s_m(mem, src));
        self
    }
    pub fn i32_load8_u_m(&mut self, mem: MemArg, src: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_load8_u_m(mem, src));
        self
    }
    pub fn i64_load(&mut self, src: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_load(src));
        self
    }
    pub fn i32_add(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_add(lhs, rhs));
        self
    }
    pub fn i32_sub(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_sub(lhs, rhs));
        self
    }
    pub fn i32_mul(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_mul(lhs, rhs));
        self
    }
    pub fn i32_div_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_div_u(lhs, rhs));
        self
    }
    pub fn i32_div_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_div_s(lhs, rhs));
        self
    }
    pub fn i32_rem_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_rem_u(lhs, rhs));
        self
    }
    pub fn i32_rem_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_rem_s(lhs, rhs));
        self
    }
    pub fn i32_and(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_and(lhs, rhs));
        self
    }
    pub fn i32_or(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_or(lhs, rhs));
        self
    }
    pub fn i32_xor(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_xor(lhs, rhs));
        self
    }
    pub fn i32_shl(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_shl(lhs, rhs));
        self
    }
    pub fn i32_shr_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_shr_u(lhs, rhs));
        self
    }
    pub fn i32_shr_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_shr_s(lhs, rhs));
        self
    }
    pub fn i32_clz(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_clz(operand));
        self
    }
    pub fn i32_ctz(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_ctz(operand));
        self
    }
    pub fn i32_popcnt(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_popcnt(operand));
        self
    }
    pub fn i32_eqz(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_eqz(operand));
        self
    }
    pub fn i32_eq(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_eq(lhs, rhs));
        self
    }
    pub fn i32_ne(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_ne(lhs, rhs));
        self
    }
    pub fn i32_lt_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_lt_u(lhs, rhs));
        self
    }
    pub fn i32_lt_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_lt_s(lhs, rhs));
        self
    }
    pub fn i32_gt_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_gt_u(lhs, rhs));
        self
    }
    pub fn i32_gt_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_gt_s(lhs, rhs));
        self
    }
    pub fn i32_le_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_le_u(lhs, rhs));
        self
    }
    pub fn i32_le_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_le_s(lhs, rhs));
        self
    }
    pub fn i32_ge_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_ge_u(lhs, rhs));
        self
    }
    pub fn i32_ge_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_ge_s(lhs, rhs));
        self
    }
    pub fn i32_add_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_add_());
        self
    }
    pub fn i32_sub_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_sub_());
        self
    }
    pub fn i32_mul_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_mul_());
        self
    }
    pub fn i32_div_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_div_u_());
        self
    }
    pub fn i32_div_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_div_s_());
        self
    }
    pub fn i32_rem_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_rem_u_());
        self
    }
    pub fn i32_rem_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_rem_s_());
        self
    }
    pub fn i32_and_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_and_());
        self
    }
    pub fn i32_or_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_or_());
        self
    }
    pub fn i32_xor_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_xor_());
        self
    }
    pub fn i32_shl_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_shl_());
        self
    }
    pub fn i32_shr_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_shr_u_());
        self
    }
    pub fn i32_shr_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_shr_s_());
        self
    }
    pub fn i32_clz_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_clz_());
        self
    }
    pub fn i32_ctz_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_ctz_());
        self
    }
    pub fn i32_popcnt_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_popcnt_());
        self
    }
    pub fn i32_eqz_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_eqz_());
        self
    }
    pub fn i32_eq_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_eq_());
        self
    }
    pub fn i32_ne_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_ne_());
        self
    }
    pub fn i32_lt_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_lt_u_());
        self
    }
    pub fn i32_lt_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_lt_s_());
        self
    }
    pub fn i32_gt_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_gt_u_());
        self
    }
    pub fn i32_gt_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_gt_s_());
        self
    }
    pub fn i32_le_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_le_u_());
        self
    }
    pub fn i32_le_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_le_s_());
        self
    }
    pub fn i32_ge_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_ge_u_());
        self
    }
    pub fn i32_ge_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i32_ge_s_());
        self
    }
    pub fn i64_add(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_add(lhs, rhs));
        self
    }
    pub fn i64_sub(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_sub(lhs, rhs));
        self
    }
    pub fn i64_mul(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_mul(lhs, rhs));
        self
    }
    pub fn i64_div_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_div_u(lhs, rhs));
        self
    }
    pub fn i64_div_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_div_s(lhs, rhs));
        self
    }
    pub fn i64_rem_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_rem_u(lhs, rhs));
        self
    }
    pub fn i64_rem_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_rem_s(lhs, rhs));
        self
    }
    pub fn i64_and(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_and(lhs, rhs));
        self
    }
    pub fn i64_or(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_or(lhs, rhs));
        self
    }
    pub fn i64_xor(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_xor(lhs, rhs));
        self
    }
    pub fn i64_shl(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_shl(lhs, rhs));
        self
    }
    pub fn i64_shr_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_shr_u(lhs, rhs));
        self
    }
    pub fn i64_shr_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_shr_s(lhs, rhs));
        self
    }
    pub fn i64_clz(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_clz(operand));
        self
    }
    pub fn i64_ctz(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_ctz(operand));
        self
    }
    pub fn i64_popcnt(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_popcnt(operand));
        self
    }
    pub fn i64_eqz(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_eqz(operand));
        self
    }
    pub fn i64_eq(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_eq(lhs, rhs));
        self
    }
    pub fn i64_ne(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_ne(lhs, rhs));
        self
    }
    pub fn i64_lt_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_lt_u(lhs, rhs));
        self
    }
    pub fn i64_lt_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_lt_s(lhs, rhs));
        self
    }
    pub fn i64_gt_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_gt_u(lhs, rhs));
        self
    }
    pub fn i64_gt_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_gt_s(lhs, rhs));
        self
    }
    pub fn i64_le_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_le_u(lhs, rhs));
        self
    }
    pub fn i64_le_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_le_s(lhs, rhs));
        self
    }
    pub fn i64_ge_u(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_ge_u(lhs, rhs));
        self
    }
    pub fn i64_ge_s(&mut self, lhs: Instruction, rhs: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i64_ge_s(lhs, rhs));
        self
    }
    pub fn i64_add_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_add_());
        self
    }
    pub fn i64_sub_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_sub_());
        self
    }
    pub fn i64_mul_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_mul_());
        self
    }
    pub fn i64_div_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_div_u_());
        self
    }
    pub fn i64_div_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_div_s_());
        self
    }
    pub fn i64_rem_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_rem_u_());
        self
    }
    pub fn i64_rem_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_rem_s_());
        self
    }
    pub fn i64_and_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_and_());
        self
    }
    pub fn i64_or_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_or_());
        self
    }
    pub fn i64_xor_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_xor_());
        self
    }
    pub fn i64_shl_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_shl_());
        self
    }
    pub fn i64_shr_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_shr_u_());
        self
    }
    pub fn i64_shr_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_shr_s_());
        self
    }
    pub fn i64_eq_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_eq_());
        self
    }
    pub fn i64_ne_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_ne_());
        self
    }
    pub fn i64_lt_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_lt_u_());
        self
    }
    pub fn i64_lt_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_lt_s_());
        self
    }
    pub fn i64_gt_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_gt_u_());
        self
    }
    pub fn i64_gt_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_gt_s_());
        self
    }
    pub fn i64_le_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_le_u_());
        self
    }
    pub fn i64_le_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_le_s_());
        self
    }
    pub fn i64_ge_u_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_ge_u_());
        self
    }
    pub fn i64_ge_s_(&mut self) -> &mut Self {
        self.instructions.push(Instruction::i64_ge_s_());
        self
    }
    // conversions
    pub fn i64_extend_i32_s(&mut self, operand: Instruction) -> &mut Self {
        self.instructions
            .push(Instruction::i64_extend_i32_s(operand));
        self
    }
    pub fn i64_extend_i32_u(&mut self, operand: Instruction) -> &mut Self {
        self.instructions
            .push(Instruction::i64_extend_i32_u(operand));
        self
    }
    pub fn i32_wrap_i64(&mut self, operand: Instruction) -> &mut Self {
        self.instructions.push(Instruction::i32_wrap_i64(operand));
        self
    }
    // locals
    pub fn local_get<T: Into<Index>>(&mut self, index: T) -> &mut Self {
        self.instructions.push(Instruction::local_get(index));
        self
    }
    pub fn local_set<T: Into<Index>>(&mut self, index: T, value: Instruction) -> &mut Self {
        self.instructions.push(Instruction::local_set(index, value));
        self
    }
    pub fn local_set_<T: Into<Index>>(&mut self, index: T) -> &mut Self {
        self.instructions.push(Instruction::local_set_(index));
        self
    }
    pub fn local_tee<T: Into<Index>>(&mut self, index: T, value: Instruction) -> &mut Self {
        self.instructions.push(Instruction::local_tee(index, value));
        self
    }
    pub fn global_get<T: Into<Index>>(&mut self, index: T) -> &mut Self {
        self.instructions.push(Instruction::global_get(index));
        self
    }
    pub fn global_set<T: Into<Index>>(&mut self, index: T, value: Instruction) -> &mut Self {
        self.instructions
            .push(Instruction::global_set(index, value));
        self
    }
    pub fn call<T: Into<Index>>(&mut self, index: T, operands: Vec<Instruction>) -> &mut Self {
        self.instructions.push(Instruction::call(index, operands));
        self
    }
    pub fn drop(&mut self) -> &mut Self {
        self.instructions.push(Instruction::drop());
        self
    }
    pub fn select(
        &mut self,
        then_value: Instruction,
        else_value: Instruction,
        cond_value: Instruction,
    ) -> &mut Self {
        self.instructions
            .push(Instruction::select(then_value, else_value, cond_value));
        self
    }
    pub fn nop(&mut self) -> &mut Self {
        self.instructions.push(Instruction::nop());
        self
    }
    pub fn unreachable(&mut self) -> &mut Self {
        self.instructions.push(Instruction::unreachable());
        self
    }
    pub fn block(&mut self, wasm_block: BlockInstruction) -> &mut Self {
        self.instructions.push(Instruction::block(wasm_block));
        self
    }
    pub fn r#loop(&mut self, wasm_loop: LoopInstruction) -> &mut Self {
        self.instructions.push(Instruction::r#loop(wasm_loop));
        self
    }
    pub fn r#if(&mut self, wasm_if: IfInstruction) -> &mut Self {
        self.instructions.push(Instruction::r#if(wasm_if));
        self
    }
    pub fn br(&mut self, label_idx: u32) -> &mut Self {
        self.instructions.push(Instruction::br(label_idx));
        self
    }
    pub fn br_if(&mut self, label_idx: u32, cond: Instruction) -> &mut Self {
        self.instructions.push(Instruction::br_if(label_idx, cond));
        self
    }
    pub fn br_if_(&mut self, label_idx: u32) -> &mut Self {
        self.instructions.push(Instruction::br_if_(label_idx));
        self
    }
    pub fn r#return(&mut self) -> &mut Self {
        self.instructions.push(Instruction::r#return());
        self
    }

    // ext: bulk-memory
    pub fn memory_copy(&mut self, n: Instruction, src: Instruction, dst: Instruction) -> &mut Self {
        self.instructions
            .push(Instruction::memory_copy(n, src, dst));
        self
    }
}

impl Instructions {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.instructions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.instructions.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&Instruction> {
        self.instructions.get(index)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Instruction> {
        self.instructions.iter()
    }

    pub fn push(&mut self, inst: Instruction) -> &mut Self {
        self.instructions.push(inst);
        self
    }

    pub fn insert(&mut self, index: usize, inst: Instruction) {
        self.instructions.insert(index, inst);
    }

    pub fn remove(&mut self, index: usize) -> Instruction {
        self.instructions.remove(index)
    }
}

impl IntoIterator for Instructions {
    type Item = Instruction;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.instructions.into_iter()
    }
}

impl Extend<Instruction> for Instructions {
    fn extend<T: IntoIterator<Item = Instruction>>(&mut self, instructions: T) {
        self.instructions.extend(instructions)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockInstruction {
    /// Structured control instructions can bind an optional symbolic
    /// label identifier. The same label identifier may optionally be
    /// repeated after the corresponding `end` and `else` pseudo instructions,
    /// to indicate the matching delimiters.
    label: Option<String>,

    /// A structured instruction can consume input and produce output on
    /// the operand stack according to its annotated block type.
    signature: FunctionSignature,
    body: Instructions,
}

impl BlockInstruction {
    pub fn new() -> Self {
        Self::with_signature(FunctionSignature::new(vec![], vec![]))
    }

    pub fn with_result(retty: Type) -> Self {
        Self::with_signature(FunctionSignature::new(vec![], vec![retty]))
    }

    // To use multiple results, you need multi-value extension.
    pub fn with_signature(signature: FunctionSignature) -> Self {
        Self {
            signature,
            body: Instructions::new(),
            label: None,
        }
    }

    pub fn label(&self) -> Option<&str> {
        self.label.as_deref()
    }
    pub fn update_label(&mut self, label: String) {
        self.label.replace(label);
    }

    pub fn signature(&self) -> &FunctionSignature {
        &self.signature
    }

    pub fn body(&self) -> &Instructions {
        &self.body
    }
    pub fn body_mut(&mut self) -> &mut Instructions {
        &mut self.body
    }
}

impl Default for BlockInstruction {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopInstruction {
    /// A structured instruction can consume input and produce output on
    /// the operand stack according to its annotated block type.
    signature: FunctionSignature,
    body: Instructions,
}

impl LoopInstruction {
    pub fn new() -> Self {
        Self::with_signature(FunctionSignature::new(vec![], vec![]))
    }

    pub fn with_result(retty: Type) -> Self {
        Self::with_signature(FunctionSignature::new(vec![], vec![retty]))
    }

    // To use multiple results, you need multi-value extension.
    pub fn with_signature(signature: FunctionSignature) -> Self {
        Self {
            signature,
            body: Instructions::new(),
        }
    }

    pub fn signature(&self) -> &FunctionSignature {
        &self.signature
    }

    pub fn body(&self) -> &Instructions {
        &self.body
    }
    pub fn body_mut(&mut self) -> &mut Instructions {
        &mut self.body
    }
}

impl Default for LoopInstruction {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfInstruction {
    /// A structured instruction can consume input and produce output on
    /// the operand stack according to its annotated block type.
    signature: FunctionSignature,
    then_body: Instructions,
    else_body: Instructions,
}

impl IfInstruction {
    pub fn new() -> Self {
        Self::with_signature(FunctionSignature::new(vec![], vec![]))
    }

    pub fn with_result(retty: Type) -> Self {
        Self::with_signature(FunctionSignature::new(vec![], vec![retty]))
    }

    // To use multiple results, you need multi-value extension.
    pub fn with_signature(signature: FunctionSignature) -> Self {
        Self {
            signature,
            then_body: Instructions::new(),
            else_body: Instructions::new(),
        }
    }

    pub fn signature(&self) -> &FunctionSignature {
        &self.signature
    }

    pub fn then_body(&self) -> &Instructions {
        &self.then_body
    }
    pub fn then_body_mut(&mut self) -> &mut Instructions {
        &mut self.then_body
    }

    pub fn else_body(&self) -> &Instructions {
        &self.else_body
    }
    pub fn else_body_mut(&mut self) -> &mut Instructions {
        &mut self.else_body
    }
}

impl Default for IfInstruction {
    fn default() -> Self {
        Self::new()
    }
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
    pub fn with_offset(offset: u32) -> Self {
        Self::new(Some(offset), None)
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

    fn enter_global(&mut self, global: &Entity<Global>);
    fn exit_global(&mut self, global: &Entity<Global>);

    fn enter_function(&mut self, function: &Entity<Function>);
    fn exit_function(&mut self, function: &Entity<Function>);
}

fn walk(visitor: &mut dyn Visitor, module: &Entity<Module>) {
    visitor.enter_module(module);

    for import in module.get().imports() {
        visitor.enter_import(import);
        visitor.exit_import(import);
    }

    for export in module.get().exports() {
        visitor.enter_export(export);
        visitor.exit_export(export);
    }

    if let Some(memory) = module.get().memory() {
        visitor.enter_memory(memory);
        visitor.exit_memory(memory);
    }

    for data_segment in module.get().data_segments() {
        visitor.enter_data_segment(data_segment);
        visitor.exit_data_segment(data_segment);
    }

    for global in module.get().globals() {
        visitor.enter_global(global);
        visitor.exit_global(global);
    }

    for function in module.get().functions() {
        visitor.enter_function(function);
        visitor.exit_function(function);
    }

    visitor.exit_module(module);
}

#[derive(Debug, Default)]
pub struct WatBuilder {
    buffer: String,
    indent: u32,
}

impl WatBuilder {
    pub fn new() -> Self {
        Self {
            buffer: String::new(),
            indent: 0,
        }
    }

    pub fn emit(&mut self, module: &Entity<Module>) -> String {
        self.buffer.clear();

        walk(self, module);
        std::mem::take(&mut self.buffer)
    }

    /// Prints a newline and indent.
    fn newline(&mut self) {
        self.buffer.push('\n');
        self.indent();
    }
    /// Prints spaces according to the current indentation level.
    fn indent(&mut self) {
        for _ in 0..self.indent {
            self.buffer.push_str("  ");
        }
    }
    /// Increases indentation level.
    fn inc_indent(&mut self) {
        self.indent += 1;
    }
    /// Decreases indentation level.
    fn decr_indent(&mut self) {
        self.indent -= 1;
    }

    fn push_indent(&mut self) {
        self.inc_indent();
        self.newline();
    }
    fn pop_indent(&mut self) {
        self.decr_indent();
        self.newline();
    }

    /// Removes training white spaces in the buffer.
    fn trim_trailing_white_spaces(&mut self) {
        while let Some(c) = self.buffer.pop() {
            if !char::is_whitespace(c) {
                self.buffer.push(c);
                break;
            }
        }
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
        let mut params = signature.params().peekable();

        while let Some(param) = params.next() {
            self.buffer.push('(');
            self.buffer.push_str("param");
            if let Some(name) = param.id() {
                self.emit_id(name);
            }
            self.emit_type(param.get());
            self.buffer.push(')');

            if params.peek().is_some() {
                self.buffer.push(' ');
            }
        }

        for ty in signature.results() {
            self.buffer.push(' ');
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
        if mem.offset().is_some() || mem.align().is_some() {
            self.buffer.push(' ');
        }
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
    fn emit_instructions<'a>(&mut self, instructions: impl Iterator<Item = &'a Instruction>) {
        let mut first = true;
        for inst in instructions {
            if !first {
                self.newline();
            } else {
                first = false;
            }
            self.emit_inst(inst);
        }
    }
    fn emit_inst(&mut self, inst: &Instruction) {
        let mut close_paren = false;
        let scoped_indent = self.indent;

        match inst.kind() {
            InstructionKind::Nop => {
                // Emit nothing for `nop`
                return;
            }
            InstructionKind::Block(block) if block.label().is_some() => {
                // A block that has a label must not be a S expression.
            }
            InstructionKind::Drop | InstructionKind::Return if !inst.has_operands() => {}
            _ => {
                self.buffer.push('(');
                close_paren = true;
            }
        }

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
            InstructionKind::I32Store8(mem) => {
                self.buffer.push_str("i32.store8");
                self.emit_mem_arg(mem);
            }
            InstructionKind::I64Store(mem) => {
                self.buffer.push_str("i64.store");
                self.emit_mem_arg(mem);
            }
            InstructionKind::I32Load(mem) => {
                self.buffer.push_str("i32.load");
                self.emit_mem_arg(mem);
            }
            InstructionKind::I32Load8S(mem) => {
                self.buffer.push_str("i32.load8_s");
                self.emit_mem_arg(mem);
            }
            InstructionKind::I32Load8U(mem) => {
                self.buffer.push_str("i32.load8_u");
                self.emit_mem_arg(mem);
            }
            InstructionKind::I64Load(mem) => {
                self.buffer.push_str("i64.load");
                self.emit_mem_arg(mem);
            }
            InstructionKind::MemoryCopy => {
                self.buffer.push_str("memory.copy");
            }
            InstructionKind::LocalGet(index) => {
                self.buffer.push_str("local.get");
                self.emit_index(index);
            }
            InstructionKind::LocalSet(index) => {
                self.buffer.push_str("local.set");
                self.emit_index(index);
            }
            InstructionKind::LocalTee(index) => {
                self.buffer.push_str("local.tee");
                self.emit_index(index);
            }
            InstructionKind::GlobalGet(index) => {
                self.buffer.push_str("global.get");
                self.emit_index(index);
            }
            InstructionKind::GlobalSet(index) => {
                self.buffer.push_str("global.set");
                self.emit_index(index);
            }
            InstructionKind::Call(index) => {
                self.buffer.push_str("call");
                self.emit_index(index);
            }
            InstructionKind::Drop => {
                self.buffer.push_str("drop");
            }
            InstructionKind::Select => {
                self.buffer.push_str("select");
            }
            InstructionKind::I32Add => {
                self.buffer.push_str("i32.add");
            }
            InstructionKind::I32Sub => {
                self.buffer.push_str("i32.sub");
            }
            InstructionKind::I32Mul => {
                self.buffer.push_str("i32.mul");
            }
            InstructionKind::I32DivU => {
                self.buffer.push_str("i32.div_u");
            }
            InstructionKind::I32DivS => {
                self.buffer.push_str("i32.div_s");
            }
            InstructionKind::I32RemU => {
                self.buffer.push_str("i32.rem_u");
            }
            InstructionKind::I32RemS => {
                self.buffer.push_str("i32.rem_s");
            }
            InstructionKind::I32And => {
                self.buffer.push_str("i32.and");
            }
            InstructionKind::I32Or => {
                self.buffer.push_str("i32.or");
            }
            InstructionKind::I32Xor => {
                self.buffer.push_str("i32.xor");
            }
            InstructionKind::I32ShiLeft => {
                self.buffer.push_str("i32.shl");
            }
            InstructionKind::I32ShiftRightU => {
                self.buffer.push_str("i32.shr_u");
            }
            InstructionKind::I32ShiftRightS => {
                self.buffer.push_str("i32.shr_s");
            }
            InstructionKind::I32RotateLeft => {
                self.buffer.push_str("i32.rotl");
            }
            InstructionKind::I32RotateRight => {
                self.buffer.push_str("i32.rotr");
            }
            InstructionKind::I32Clz => {
                self.buffer.push_str("i32.clz");
            }
            InstructionKind::I32Ctz => {
                self.buffer.push_str("i32.ctz");
            }
            InstructionKind::I32PopCnt => {
                self.buffer.push_str("i32.popcnt");
            }
            InstructionKind::I32Eqz => {
                self.buffer.push_str("i32.eqz");
            }
            InstructionKind::I32Eq => {
                self.buffer.push_str("i32.eq");
            }
            InstructionKind::I32Ne => {
                self.buffer.push_str("i32.ne");
            }
            InstructionKind::I32LtU => {
                self.buffer.push_str("i32.lt_u");
            }
            InstructionKind::I32LtS => {
                self.buffer.push_str("i32.lt_s");
            }
            InstructionKind::I32GtU => {
                self.buffer.push_str("i32.gt_u");
            }
            InstructionKind::I32GtS => {
                self.buffer.push_str("i32.gt_s");
            }
            InstructionKind::I32LeU => {
                self.buffer.push_str("i32.le_u");
            }
            InstructionKind::I32LeS => {
                self.buffer.push_str("i32.le_s");
            }
            InstructionKind::I32GeU => {
                self.buffer.push_str("i32.ge_u");
            }
            InstructionKind::I32GeS => {
                self.buffer.push_str("i32.ge_s");
            }
            InstructionKind::I64Add => {
                self.buffer.push_str("i64.add");
            }
            InstructionKind::I64Sub => {
                self.buffer.push_str("i64.sub");
            }
            InstructionKind::I64Mul => {
                self.buffer.push_str("i64.mul");
            }
            InstructionKind::I64DivU => {
                self.buffer.push_str("i64.div_u");
            }
            InstructionKind::I64DivS => {
                self.buffer.push_str("i64.div_s");
            }
            InstructionKind::I64RemU => {
                self.buffer.push_str("i64.rem_u");
            }
            InstructionKind::I64RemS => {
                self.buffer.push_str("i64.rem_s");
            }
            InstructionKind::I64And => {
                self.buffer.push_str("i64.and");
            }
            InstructionKind::I64Or => {
                self.buffer.push_str("i64.or");
            }
            InstructionKind::I64Xor => {
                self.buffer.push_str("i64.xor");
            }
            InstructionKind::I64ShiLeft => {
                self.buffer.push_str("i64.shl");
            }
            InstructionKind::I64ShiftRightU => {
                self.buffer.push_str("i64.shr_u");
            }
            InstructionKind::I64ShiftRightS => {
                self.buffer.push_str("i64.shr_s");
            }
            InstructionKind::I64RotateLeft => {
                self.buffer.push_str("i64.rotl");
            }
            InstructionKind::I64RotateRight => {
                self.buffer.push_str("i64.rotr");
            }
            InstructionKind::I64Clz => {
                self.buffer.push_str("i64.clz");
            }
            InstructionKind::I64Ctz => {
                self.buffer.push_str("i64.ctz");
            }
            InstructionKind::I64PopCnt => {
                self.buffer.push_str("i64.popcnt");
            }
            InstructionKind::I64Eqz => {
                self.buffer.push_str("i64.eqz");
            }
            InstructionKind::I64Eq => {
                self.buffer.push_str("i64.eq");
            }
            InstructionKind::I64Ne => {
                self.buffer.push_str("i64.ne");
            }
            InstructionKind::I64LtU => {
                self.buffer.push_str("i64.lt_u");
            }
            InstructionKind::I64LtS => {
                self.buffer.push_str("i64.lt_s");
            }
            InstructionKind::I64GtU => {
                self.buffer.push_str("i64.gt_u");
            }
            InstructionKind::I64GtS => {
                self.buffer.push_str("i64.gt_s");
            }
            InstructionKind::I64LeU => {
                self.buffer.push_str("i64.le_u");
            }
            InstructionKind::I64LeS => {
                self.buffer.push_str("i64.le_s");
            }
            InstructionKind::I64GeU => {
                self.buffer.push_str("i64.ge_u");
            }
            InstructionKind::I64GeS => {
                self.buffer.push_str("i64.ge_s");
            }
            // conversions
            InstructionKind::I64ExtendI32S => {
                self.buffer.push_str("i64.extend_i32_s");
            }
            InstructionKind::I64ExtendI32U => {
                self.buffer.push_str("i64.extend_i32_u");
            }
            InstructionKind::I32WrapI64 => {
                self.buffer.push_str("i32.wrap_i64");
            }
            InstructionKind::Nop => {
                self.buffer.push_str("nop");
            }
            InstructionKind::Unreachable => {
                self.buffer.push_str("unreachable");
            }
            InstructionKind::Br(label_idx) => {
                self.buffer.push_str("br");
                self.buffer.push(' ');
                self.buffer.push_str(&label_idx.to_string());
            }
            InstructionKind::BrIf(label_idx) => {
                self.buffer.push_str("br_if");
                self.buffer.push(' ');
                self.buffer.push_str(&label_idx.to_string());
            }
            InstructionKind::If(ctrl) => {
                self.buffer.push_str("if");
                self.emit_function_signature(ctrl.signature());
                self.push_indent();
                self.emit_instructions(ctrl.then_body().iter());
            }
            InstructionKind::Loop(ctrl) => {
                self.buffer.push_str("loop");
                self.emit_function_signature(ctrl.signature());
                self.push_indent();
                self.emit_instructions(ctrl.body().iter());
            }
            InstructionKind::Block(block) => {
                self.buffer.push_str("block");
                if let Some(label) = block.label() {
                    self.emit_id(label);
                }
                self.emit_function_signature(block.signature());
                self.push_indent();
                self.emit_instructions(block.body().iter());

                if let Some(label) = block.label() {
                    self.pop_indent();
                    self.buffer.push_str("end");
                    self.emit_id(label);
                }
            }
            InstructionKind::Return => {
                self.buffer.push_str("return");
            }
        }

        for operand in inst.operands() {
            self.buffer.push(' ');
            self.emit_inst(operand);
        }

        if close_paren {
            // Pop indent automatically.
            for _ in scoped_indent..self.indent {
                self.pop_indent();
            }
            self.trim_trailing_white_spaces();
            self.buffer.push(')');
        }
    }
}

impl Visitor for WatBuilder {
    fn enter_module(&mut self, module: &Entity<Module>) {
        self.buffer.push('(');
        self.buffer.push_str("module");

        if let Some(name) = module.id() {
            self.emit_id(name);
        }
        self.push_indent();
    }
    fn exit_module(&mut self, _module: &Entity<Module>) {
        self.pop_indent();
        self.trim_trailing_white_spaces();
        self.buffer.push(')');
    }

    fn enter_import(&mut self, import: &Import) {
        self.buffer.push('(');
        self.buffer.push_str("import");

        self.emit_str(import.module());
        self.emit_str(import.name());
        self.push_indent();

        match import.desc() {
            ImportDesc::Function(fun) => self.emit_import_desc_function(fun),
        }
    }
    fn exit_import(&mut self, _import: &Import) {
        self.pop_indent();
        self.trim_trailing_white_spaces();
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
        self.newline();
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
        self.newline();
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
        self.newline();
    }

    fn enter_function(&mut self, fun: &Entity<Function>) {
        self.buffer.push('(');
        self.buffer.push_str("func");

        // id
        if let Some(name) = fun.id() {
            self.emit_id(name);
        }

        for export in fun.get().exports() {
            self.buffer.push(' ');
            self.buffer.push('(');
            self.buffer.push_str("export");
            self.emit_str(export);
            self.buffer.push(')');
        }

        self.emit_function_signature(fun.get().signature());
        self.push_indent();

        // locals
        let mut locals = fun.get().locals().peekable();

        while let Some(local) = locals.next() {
            self.buffer.push('(');
            self.buffer.push_str("local");
            if let Some(name) = local.id() {
                self.emit_id(name);
            }
            self.emit_type(local.get());
            self.buffer.push(')');

            if locals.peek().is_some() {
                self.buffer.push(' ');
            }
        }
        if fun.get().locals().len() != 0 {
            self.newline();
            self.newline();
        }

        // instructions
        let mut instructions = fun.get().body().iter().peekable();

        while let Some(inst) = instructions.next() {
            self.emit_inst(inst);
            if instructions.peek().is_some() {
                self.newline();
            }
        }
    }
    fn exit_function(&mut self, _function: &Entity<Function>) {
        self.buffer.push(')');
        self.pop_indent();
    }

    fn enter_global(&mut self, global: &Entity<Global>) {
        self.buffer.push('(');
        self.buffer.push_str("global");

        // id
        if let Some(name) = global.id() {
            self.emit_id(name);
        }

        // typ
        if global.get().is_mutable() {
            self.buffer.push(' ');
            self.buffer.push('(');
            self.buffer.push_str("mut");
            self.emit_type(global.get().ty());
            self.buffer.push(')');
        } else {
            self.emit_type(global.get().ty());
        }

        self.buffer.push(' ');
        for inst in global.get().initializer() {
            self.emit_inst(inst);
        }
    }
    fn exit_global(&mut self, _global: &Entity<Global>) {
        self.buffer.push(')');
        self.newline();
    }
}
