use std::fmt;
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
            Type::Struct(struct_ty) => {
                write!(f, "struct {} ", struct_ty.name())?;

                let mut it = struct_ty.fields().peekable();
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
    }
}

pub type StructTyField<'tcx> = (String, &'tcx Type<'tcx>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructTy<'tcx> {
    name: String,
    fields: Vec<StructTyField<'tcx>>,
}

impl<'tcx> StructTy<'tcx> {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fields(&self) -> impl Iterator<Item = &StructTyField<'tcx>> {
        self.fields.iter()
    }
}
