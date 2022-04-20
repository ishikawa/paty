//! WebAssembly
//! https://webassembly.github.io/spec/core/intro/introduction.html

use std::fmt;

/// Wraps a construct with a referenced identifier.
///
/// Some constructs in WAT can be referenced by an identifier. This
/// struct wraps a construct with a referenced identifier.
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
    memory: Option<Entity<Memory>>,
}

impl Module {
    pub fn new(imports: Vec<Import>, memory: Option<Entity<Memory>>) -> Self {
        Self { imports, memory }
    }

    pub fn imports(&self) -> impl ExactSizeIterator<Item = &Import> {
        self.imports.iter()
    }

    pub fn memory(&self) -> Option<&Entity<Memory>> {
        self.memory.as_ref()
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

pub trait Visitor {
    fn enter_module(&mut self, module: &Entity<Module>);
    fn exit_module(&mut self, module: &Entity<Module>);

    fn enter_import(&mut self, import: &Import);
    fn exit_import(&mut self, import: &Import);

    fn enter_memory(&mut self, memory: &Entity<Memory>);
    fn exit_memory(&mut self, memory: &Entity<Memory>);
}

fn walk(visitor: &mut dyn Visitor, module: &Entity<Module>) {
    visitor.enter_module(module);

    // imports
    for import in module.get().imports() {
        visitor.enter_import(import);
        visitor.exit_import(import);
    }

    // memory
    if let Some(memory) = module.get().memory() {
        visitor.enter_memory(memory);
        visitor.exit_memory(memory);
    }

    visitor.exit_module(module);
}

#[derive(Debug)]
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

    fn emit_id(&mut self, id: &str) {
        self.buffer.push('$');
        self.buffer.push_str(id);
    }
    fn emit_str(&mut self, s: &str) {
        self.buffer.push('"');
        for c in s.escape_default() {
            self.buffer.push(c);
        }
        self.buffer.push('"');
    }
    fn emit_type(&mut self, ty: &Type) {
        self.buffer.push_str(match ty {
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::F32 => "f32",
            Type::F64 => "f64",
        });
    }
    fn emit_limits(&mut self, limits: &Limits) {
        self.buffer.push_str(&limits.min().to_string());

        if let Some(max) = limits.max() {
            self.buffer.push(' ');
            self.buffer.push_str(&max.to_string());
        }
    }
    fn emit_import_desc_function(&mut self, fun: &Entity<FunctionSignature>) {
        self.buffer.push('(');
        self.buffer.push_str("func");

        if let Some(name) = fun.id() {
            self.buffer.push(' ');
            self.emit_id(name);
        }
        self.buffer.push(' ');

        for param in fun.get().params() {
            self.buffer.push('(');
            self.buffer.push_str("param");
            self.buffer.push(' ');
            if let Some(name) = param.id() {
                self.emit_id(name);
                self.buffer.push(' ');
            }
            self.emit_type(param.get());
            self.buffer.push(')');
        }

        for ty in fun.get().results() {
            self.buffer.push('(');
            self.buffer.push_str("result");
            self.buffer.push(' ');
            self.emit_type(ty);
            self.buffer.push(')');
        }

        self.buffer.push(')');
    }
}

impl Visitor for WatBuilder {
    fn enter_module(&mut self, module: &Entity<Module>) {
        self.buffer.push('(');
        self.buffer.push_str("module");

        if let Some(name) = module.id() {
            self.buffer.push(' ');
            self.emit_id(name);
        }
    }
    fn exit_module(&mut self, _module: &Entity<Module>) {
        self.buffer.push(')');
    }

    fn enter_import(&mut self, import: &Import) {
        self.buffer.push('(');
        self.buffer.push_str("import");

        self.buffer.push(' ');
        self.emit_str(import.module());
        self.buffer.push(' ');
        self.emit_str(import.name());
        self.buffer.push(' ');

        match import.desc() {
            ImportDesc::Function(fun) => self.emit_import_desc_function(fun),
        }
    }
    fn exit_import(&mut self, _import: &Import) {
        self.buffer.push(')');
    }

    fn enter_memory(&mut self, memory: &Entity<Memory>) {
        self.buffer.push('(');
        self.buffer.push_str("memory");

        self.buffer.push(' ');
        if let Some(name) = memory.id() {
            self.buffer.push(' ');
            self.emit_id(name);
        }

        self.emit_limits(memory.get().limits());
    }
    fn exit_memory(&mut self, _memory: &Entity<Memory>) {
        self.buffer.push(')');
    }
}
