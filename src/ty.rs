use std::hash::{Hash, Hasher};
use std::{cell::Cell, fmt};
use typed_arena::Arena;

#[derive(Clone, Copy)]
pub struct TypeContext<'tcx> {
    pub type_arena: &'tcx Arena<Type<'tcx>>,
}

impl<'tcx> TypeContext<'tcx> {
    pub fn new(type_arena: &'tcx Arena<Type<'tcx>>) -> Self {
        Self { type_arena }
    }

    pub fn int64(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Int64)
    }

    pub fn boolean(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Boolean)
    }

    pub fn string(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::String)
    }

    pub fn undetermined(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Undetermined)
    }

    pub fn tuple(&self, value_types: &[&'tcx Type<'tcx>]) -> &'tcx Type<'tcx> {
        self.type_arena
            .alloc(Type::Tuple(value_types.iter().copied().collect()))
    }

    /// Returns a tuple type whose element type is unknown but has N elements.
    pub fn tuple_n(&self, n: usize) -> &'tcx Type<'tcx> {
        let mut value_types = vec![];
        let undetermined = &*self.type_arena.alloc(Type::Undetermined);

        for _ in 0..n {
            value_types.push(undetermined);
        }

        self.tuple(&value_types)
    }

    pub fn native_int(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::NativeInt)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type<'tcx> {
    /// 64bit integer
    Int64,
    /// `true` or `false`
    Boolean,
    /// string
    String,
    /// tuple
    Tuple(Vec<&'tcx Type<'tcx>>),
    /// struct
    Struct(StructTy<'tcx>),

    /// Type is specified by name and should be resolved in the later phase
    Named(NamedTy<'tcx>),

    /// Type is not specified and should be inferred in the later phase.
    Undetermined,

    // C types for internal uses
    /// int
    NativeInt,
}

impl fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int64 => write!(f, "int64"),
            Type::Boolean => write!(f, "boolean"),
            Type::String => write!(f, "string"),
            Type::NativeInt => write!(f, "int"),
            Type::Named(named_ty) => named_ty.fmt(f),
            Type::Undetermined => write!(f, "_"),
            Type::Tuple(value_types) => {
                let mut it = value_types.iter().peekable();
                write!(f, "(")?;
                while let Some(ty) = it.next() {
                    write!(f, "{}", ty)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            Type::Struct(struct_ty) => struct_ty.fmt(f),
        }
    }
}

pub type StructTyField<'tcx> = (String, &'tcx Type<'tcx>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructTy<'tcx> {
    name: String,
    fields: Vec<StructTyField<'tcx>>,
}

impl<'tcx> StructTy<'tcx> {
    pub fn new(name: &str, fields: Vec<StructTyField<'tcx>>) -> Self {
        Self {
            name: name.to_string(),
            fields,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fields(&self) -> impl Iterator<Item = &StructTyField<'tcx>> {
        self.fields.iter()
    }
}

impl fmt::Display for StructTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "struct {} ", self.name())?;

        let mut it = self.fields().peekable();
        write!(f, "{{")?;
        while let Some((fname, ty)) = it.next() {
            write!(f, "{}: ", fname)?;
            write!(f, "{}", ty)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedTy<'tcx> {
    name: String,
    ty: Cell<Option<&'tcx Type<'tcx>>>,
}

impl<'tcx> NamedTy<'tcx> {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            ty: Cell::new(None),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> Option<&'tcx Type<'tcx>> {
        self.ty.get()
    }

    pub fn expect_ty(&self) -> &'tcx Type<'tcx> {
        self.ty().unwrap_or_else(|| {
            panic!(
                "Semantic analyzer couldn't assign type for named type `{}`",
                self.name
            );
        })
    }

    pub fn assign_ty(&self, ty: &'tcx Type<'tcx>) {
        self.ty.set(Some(ty))
    }
}

impl Hash for NamedTy<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl fmt::Display for NamedTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)
    }
}
