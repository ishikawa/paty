use itertools::Itertools;
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

    #[inline]
    pub fn int64(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Int64)
    }
    #[inline]
    pub fn boolean(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Boolean)
    }
    #[inline]
    pub fn string(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::String)
    }
    #[inline]
    pub fn literal_int64(&self, value: i64) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::LiteralInt64(value))
    }
    #[inline]
    pub fn literal_boolean(&self, value: bool) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::LiteralBoolean(value))
    }
    #[inline]
    pub fn literal_string(&self, value: String) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::LiteralString(value))
    }
    #[inline]
    pub fn undetermined(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Undetermined)
    }
    #[inline]
    pub fn tuple(&self, value_types: Vec<&'tcx Type<'tcx>>) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Tuple(value_types))
    }
    #[inline]
    /// Returns a struct type whose name is `name` and has no value.
    pub fn empty_struct_ty(&self, name: String) -> &'tcx Type<'tcx> {
        let struct_ty = StructTy::new_named(name, vec![]);
        self.type_arena.alloc(Type::Struct(struct_ty))
    }
    #[inline]
    pub fn empty_anon_struct_ty(&self) -> &'tcx Type<'tcx> {
        self.anon_struct_ty(vec![])
    }
    #[inline]
    pub fn anon_struct_ty(&self, fields: Vec<TypedField<'tcx>>) -> &'tcx Type<'tcx> {
        let struct_ty = StructTy::new_anonymous(fields);
        self.type_arena.alloc(Type::Struct(struct_ty))
    }
    #[inline]
    pub fn struct_ty(&self, name: String, fields: Vec<TypedField<'tcx>>) -> &'tcx Type<'tcx> {
        let struct_ty = StructTy::new_named(name, fields);
        self.type_arena.alloc(Type::Struct(struct_ty))
    }
    #[inline]
    pub fn unit(&self) -> &'tcx Type<'tcx> {
        self.tuple_n(0)
    }
    #[inline]
    pub fn native_int(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::NativeInt)
    }
    #[inline]
    pub fn named(&self, name: String, ty: &'tcx Type<'tcx>) -> &'tcx Type<'tcx> {
        let named_ty = NamedTy::new(name);
        named_ty.assign_ty(ty);
        self.type_arena.alloc(Type::Named(named_ty))
    }

    /// Creates an union type from types. Returns the first type if types has
    /// only one element.
    /// panic if member_types is empty.
    pub fn union(
        &self,
        member_types: impl IntoIterator<Item = &'tcx Type<'tcx>>,
    ) -> &'tcx Type<'tcx> {
        // Finally, the array should contain the fewest number of types. Iterates given types and
        // adds a subsequent type if there is no type wider than that type.
        let member_types = flatten_union_ty(member_types);
        let mut tys: Vec<&Type<'_>> = vec![];

        'outer: for (i, t1) in member_types.iter().enumerate() {
            for t2 in member_types.iter().skip(i + 1) {
                if t1.is_assignable_to(t2) {
                    continue 'outer;
                }
            }
            for t2 in tys.iter() {
                if t1.is_assignable_to(t2) {
                    continue 'outer;
                }
            }
            tys.push(*t1);
        }
        assert!(!tys.is_empty());

        if tys.len() == 1 {
            tys[0]
        } else {
            self.type_arena.alloc(Type::Union(tys))
        }
    }

    /// Returns a tuple type whose element type is unknown but has N elements.
    pub fn tuple_n(&self, n: usize) -> &'tcx Type<'tcx> {
        let mut value_types = vec![];

        if n > 0 {
            let undetermined = &*self.type_arena.alloc(Type::Undetermined);

            for _ in 0..n {
                value_types.push(undetermined);
            }
        }

        self.tuple(value_types)
    }
}

#[derive(Debug, Clone, Eq)]
pub enum Type<'tcx> {
    /// 64bit integer
    Int64,
    /// `true` or `false`
    Boolean,
    String,
    Tuple(Vec<&'tcx Type<'tcx>>),
    Struct(StructTy<'tcx>),
    Union(Vec<&'tcx Type<'tcx>>),

    /// Type is specified by name and should be resolved in the later phase
    Named(NamedTy<'tcx>),

    // Literal types
    LiteralInt64(i64),
    LiteralBoolean(bool),
    LiteralString(String),

    /// Type is not specified and should be inferred in the later phase.
    Undetermined,

    // C types for internal uses
    /// int
    NativeInt,
}

impl<'tcx> Type<'tcx> {
    pub fn bottom_ty(&self) -> &Type<'tcx> {
        if let Type::Named(named_ty) = self {
            if let Some(ty) = named_ty.ty() {
                ty.bottom_ty()
            } else {
                self
            }
        } else {
            self
        }
    }

    pub fn tuple_ty(&self) -> Option<&[&Type<'tcx>]> {
        if let Type::Tuple(fs) = self.bottom_ty() {
            Some(fs)
        } else {
            None
        }
    }

    pub fn struct_ty(&self) -> Option<&StructTy<'tcx>> {
        if let Type::Struct(struct_ty) = self.bottom_ty() {
            Some(struct_ty)
        } else {
            None
        }
    }

    /// Returns `true` if the type is zero-sized.
    pub fn is_zero_sized(&self) -> bool {
        match self {
            Type::Int64
            | Type::Boolean
            | Type::String
            | Type::LiteralInt64(_)
            | Type::LiteralBoolean(_)
            | Type::LiteralString(_)
            | Type::NativeInt => false,
            Type::Tuple(fs) => fs.iter().all(|x| x.is_zero_sized()),
            Type::Struct(struct_ty) => struct_ty.fields().iter().all(|f| f.ty().is_zero_sized()),
            Type::Union(ms) => ms.iter().all(|x| x.is_zero_sized()),
            Type::Named(named_ty) => {
                if let Some(ty) = named_ty.ty() {
                    ty.is_zero_sized()
                } else {
                    true
                }
            }
            Type::Undetermined => false,
        }
    }

    /// Returns `true` if both types are compatible on its value representation.
    /// It should be consistent with promote_type().
    pub fn is_compatible(&self, other: &Self) -> bool {
        match (self, other) {
            // Primitive types
            (Type::LiteralInt64(_), Type::Int64 | Type::NativeInt)
            | (Type::LiteralBoolean(_), Type::Boolean)
            | (Type::LiteralString(_), Type::String) => true,
            (Type::Int64 | Type::NativeInt, Type::LiteralInt64(_))
            | (Type::Boolean, Type::LiteralBoolean(_))
            | (Type::String, Type::LiteralString(_)) => true,
            (Type::LiteralInt64(_), Type::LiteralInt64(_))
            | (Type::LiteralBoolean(_), Type::LiteralBoolean(_))
            | (Type::LiteralString(_), Type::LiteralString(_)) => true,
            // Compound types
            (Type::Tuple(t1), Type::Tuple(t2)) => {
                t1.len() == t2.len() && t1.iter().zip(t2).all(|(a, b)| a.is_compatible(b))
            }
            (Type::Struct(l0), Type::Struct(r0)) => {
                // Different named structs are incompatible.
                if l0.name() != r0.name() {
                    return false;
                }
                // Is assignable by structural.
                if l0.fields().len() != r0.fields().len() {
                    return false;
                }
                l0.fields()
                    .iter()
                    .zip(r0.fields())
                    .all(|(a, b)| a.name() == b.name() && a.ty().is_compatible(b.ty()))
            }
            // union type
            (Type::Union(l0), other_ty) => l0.iter().all(|x| x.is_compatible(other_ty)),
            (x, Type::Union(ms)) => ms.iter().any(|m| x.is_compatible(m)),
            // named type
            (Type::Named(named_ty1), ty2) => {
                let ty1 = named_ty1.ty().unwrap_or_else(|| {
                    panic!("Named type `{:?}` was not resolved yet.", named_ty1)
                });
                ty1.is_compatible(ty2)
            }
            (ty1, Type::Named(named_ty2)) => {
                let ty2 = named_ty2.ty().unwrap_or_else(|| {
                    panic!("Named type `{:?}` was not resolved yet.", named_ty2)
                });
                ty1.is_compatible(ty2)
            }
            (Type::Undetermined, _) | (_, Type::Undetermined) => false,
            _ => self == other,
        }
    }

    /// Returns `true` if the type can be assigned to the `other` type.
    /// A type can be assigned to other type if the type is compatible to other.
    pub fn is_assignable_to(&self, other: &Self) -> bool {
        match (self, other) {
            // Widening type
            (Self::LiteralInt64(_), Self::Int64)
            | (Self::LiteralInt64(_), Self::NativeInt)
            | (Self::LiteralBoolean(_), Self::Boolean)
            | (Self::LiteralString(_), Self::String) => true,
            // Compound types
            (Self::Tuple(t1), Self::Tuple(t2)) => {
                t1.len() == t2.len() && t1.iter().zip(t2).all(|(a, b)| a.is_assignable_to(b))
            }
            (Self::Struct(l0), Self::Struct(r0)) => {
                // Different named structs are incompatible.
                if l0.name() != r0.name() {
                    return false;
                }
                // Is assignable by structural.
                if l0.fields().len() != r0.fields().len() {
                    return false;
                }
                l0.fields()
                    .iter()
                    .zip(r0.fields())
                    .all(|(a, b)| a.name() == b.name() && a.ty().is_assignable_to(b.ty()))
            }
            // union type
            (Self::Union(l0), other_ty) => l0.iter().all(|x| x.is_assignable_to(other_ty)),
            (x, Self::Union(ms)) => ms.iter().any(|m| x.is_assignable_to(m)),
            // named type
            (Self::Named(named_ty1), ty2) => {
                let ty1 = named_ty1.ty().unwrap_or_else(|| {
                    panic!("Named type `{:?}` was not resolved yet.", named_ty1)
                });
                ty1.is_assignable_to(ty2)
            }
            (ty1, Self::Named(named_ty2)) => {
                let ty2 = named_ty2.ty().unwrap_or_else(|| {
                    panic!("Named type `{:?}` was not resolved yet.", named_ty2)
                });
                ty1.is_assignable_to(ty2)
            }
            (Self::Undetermined, _) | (_, Self::Undetermined) => false,
            // Others
            _ => self == other,
        }
    }

    /// Returns `true` if a given type can be narrowed to other type.
    pub fn can_be_narrowed_to(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (Type::Int64, Type::LiteralInt64(_))
                | (Type::NativeInt, Type::LiteralInt64(_))
                | (Type::Boolean, Type::LiteralBoolean(_))
                | (Type::String, Type::LiteralString(_))
        )
    }
}

impl PartialEq for Type<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::LiteralInt64(l0), Self::LiteralInt64(r0)) => l0 == r0,
            (Self::LiteralBoolean(l0), Self::LiteralBoolean(r0)) => l0 == r0,
            (Self::LiteralString(l0), Self::LiteralString(r0)) => l0 == r0,
            (Self::Tuple(l0), Self::Tuple(r0)) => l0 == r0,
            (Self::Struct(l0), Self::Struct(r0)) => l0 == r0,
            (Self::Union(l0), Self::Union(r0)) => l0 == r0,
            (Self::Named(named_ty1), Self::Named(named_ty2)) => {
                named_ty1.name() == named_ty2.name()
                    || named_ty1
                        .ty()
                        .and_then(|ty1| named_ty2.ty().filter(|ty2| *ty2 == ty1))
                        .is_some()
            }
            (Self::Named(named_ty1), ty2) => {
                if let Some(ty1) = named_ty1.ty() {
                    ty1 == ty2
                } else {
                    false
                }
            }
            (ty1, Self::Named(named_ty2)) => {
                if let Some(ty2) = named_ty2.ty() {
                    ty1 == ty2
                } else {
                    false
                }
            }
            (Self::Undetermined, _) | (_, Self::Undetermined) => false,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl Hash for Type<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Tuple(fs) => fs.hash(state),
            Self::Struct(struct_ty) => struct_ty.hash(state),
            Self::Union(ms) => ms.hash(state),
            Self::Named(named_ty) => {
                if let Some(ty) = named_ty.ty() {
                    ty.hash(state)
                } else {
                    named_ty.name().hash(state)
                }
            }
            Self::LiteralInt64(n) => n.hash(state),
            Self::LiteralBoolean(b) => b.hash(state),
            Self::LiteralString(s) => s.hash(state),
            Self::Int64 | Self::Boolean | Self::String | Self::Undetermined | Self::NativeInt => {
                core::mem::discriminant(self).hash(state)
            }
        }
    }
}

impl fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int64 => write!(f, "int64"),
            Self::Boolean => write!(f, "boolean"),
            Self::String => write!(f, "string"),
            Self::NativeInt => write!(f, "int"),
            Self::Named(named_ty) => named_ty.fmt(f),
            Self::Undetermined => write!(f, "_"),
            Self::Tuple(value_types) => {
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
            Self::Struct(struct_ty) => struct_ty.fmt(f),
            Self::Union(member_types) => {
                let mut it = member_types.iter().peekable();

                while let Some(ty) = it.next() {
                    write!(f, "{}", ty)?;
                    if it.peek().is_some() {
                        write!(f, " | ")?;
                    }
                }
                Ok(())
            }
            Self::LiteralInt64(n) => n.fmt(f),
            Self::LiteralBoolean(b) => b.fmt(f),
            Self::LiteralString(s) => write!(f, "\"{}\"", s.escape_default()),
        }
    }
}

// TODO: Move to ty::UnionTy
pub fn flatten_union_ty<'tcx>(
    member_types: impl IntoIterator<Item = &'tcx Type<'tcx>>,
) -> Vec<&'tcx Type<'tcx>> {
    _expand_union_ty(member_types, false)
}
pub fn expand_union_ty<'tcx>(
    member_types: impl IntoIterator<Item = &'tcx Type<'tcx>>,
) -> Vec<&'tcx Type<'tcx>> {
    _expand_union_ty(member_types, true)
}
pub fn expand_union_ty_array<'tcx>(member_types: &[&'tcx Type<'tcx>]) -> Vec<&'tcx Type<'tcx>> {
    _expand_union_ty(member_types.iter().copied(), true)
}
fn _expand_union_ty<'tcx>(
    member_types: impl IntoIterator<Item = &'tcx Type<'tcx>>,
    expand_named_ty: bool,
) -> Vec<&'tcx Type<'tcx>> {
    fn expand<'tcx>(ty: &'tcx Type<'tcx>, vec: &mut Vec<&'tcx Type<'tcx>>, expand_named_ty: bool) {
        match ty {
            Type::Named(named_ty) if expand_named_ty => {
                expand(named_ty.expect_ty(), vec, expand_named_ty);
            }
            Type::Union(tys) => {
                for t in tys {
                    expand(t, vec, expand_named_ty);
                }
            }
            _ => vec.push(ty),
        }
    }

    let mut tys = Vec::new();
    for mty in member_types {
        expand(mty, &mut tys, expand_named_ty);
    }
    tys.into_iter().unique().collect()
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypedField<'tcx> {
    name: String,
    ty: &'tcx Type<'tcx>,
}

impl<'tcx> TypedField<'tcx> {
    pub fn new(name: String, ty: &'tcx Type<'tcx>) -> Self {
        Self { name, ty }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }
}

impl fmt::Display for TypedField<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.name)?;
        write!(f, "{}", self.ty)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructTy<'tcx> {
    name: Option<String>,
    fields: Vec<TypedField<'tcx>>,
}

impl<'tcx> StructTy<'tcx> {
    pub fn new_anonymous(fields: Vec<TypedField<'tcx>>) -> Self {
        Self::new(None, fields)
    }

    pub fn new_named(name: String, fields: Vec<TypedField<'tcx>>) -> Self {
        Self::new(Some(name), fields)
    }

    pub fn new(name: Option<String>, fields: Vec<TypedField<'tcx>>) -> Self {
        if name.is_none() {
            // The order of fields must be sorted so that anonymous struct can be
            // matched by structural.
            let mut fs = fields;
            fs.sort_by(|a, b| a.name().cmp(b.name()));
            Self { name, fields: fs }
        } else {
            Self { name, fields }
        }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn fields(&self) -> &[TypedField<'tcx>] {
        self.fields.as_slice()
    }

    pub fn get_field(&self, name: &str) -> Option<&TypedField<'tcx>> {
        self.fields.iter().find(|f| f.name() == name)
    }
}

impl fmt::Display for StructTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name() {
            write!(f, "struct {} ", name)?;
        }

        let mut it = self.fields().iter().peekable();
        let empty = it.peek().is_none();

        write!(f, "{{")?;
        if !empty {
            write!(f, " ")?;
        }
        while let Some(field) = it.next() {
            write!(f, "{}", field)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        if !empty {
            write!(f, " ")?;
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
    pub fn new(name: String) -> Self {
        Self {
            name,
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

impl fmt::Display for NamedTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)
    }
}

/// The signature of a function is a combination of the function name and
/// the order of the types of the function's parameters. The type of the return
/// value of the function is irrelevant to the signature.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionSignature<'tcx> {
    name: String,
    params: Vec<&'tcx Type<'tcx>>,
}

impl<'tcx> FunctionSignature<'tcx> {
    pub fn new(name: String, params: Vec<&'tcx Type<'tcx>>) -> Self {
        Self { name, params }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn params(&self) -> &[&'tcx Type<'tcx>] {
        &self.params
    }
}

impl fmt::Display for FunctionSignature<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)?;
        write!(f, "(")?;

        let mut it = self.params.iter().peekable();

        while let Some(ty) = it.next() {
            ty.fmt(f)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod tests_types {
    use super::*;

    /// Unresolved type aliases are equated by name only.
    #[test]
    fn unresolved_named_type_eq() {
        let named_ty1 = Type::Named(NamedTy::new("T1".into()));
        let named_ty2 = Type::Named(NamedTy::new("T2".into()));

        assert!(named_ty1 == named_ty1);
        assert!(named_ty2 == named_ty2);
        assert!(named_ty1 != named_ty2);
        assert!(named_ty2 != named_ty1);
    }

    /// Resolved type aliases are equated by name and actual type.
    #[test]
    fn resolved_named_type_eq() {
        let named_ty1 = NamedTy::new("T1".into());
        named_ty1.assign_ty(&Type::Int64);
        let named_ty2 = NamedTy::new("T2".into());
        named_ty2.assign_ty(&Type::Int64);

        let ty1 = Type::Named(named_ty1);
        let ty2 = Type::Named(named_ty2);

        assert!(ty1 == ty1);
        assert!(ty2 == ty2);
        assert!(ty1 == ty2);
        assert!(ty2 == ty1);
    }

    /// ```ignore
    /// type A = 1 | 2 | 3;
    /// type B = 1 | 2;
    /// a = b // ok
    /// ```
    #[test]
    fn union_type_assignable_partially_matched_literal_types() {
        let one = Type::LiteralInt64(1);
        let two = Type::LiteralInt64(2);
        let three = Type::LiteralInt64(3);

        let a = Type::Union(vec![&one, &two, &three]);
        let b = Type::Union(vec![&one, &two]);

        assert!(b.is_assignable_to(&a));
        assert!(!a.is_assignable_to(&b));
    }

    /// ```ignore
    /// type T = [int64, int64] | [string, int64];
    /// type U = [int64 | string, int64];
    /// u = t // ok
    /// t = u // not ok
    /// ```
    #[test]
    fn union_type_assignable_tuple() {
        let t0 = Type::Tuple(vec![&Type::Int64, &Type::Int64]);
        let t1 = Type::Tuple(vec![&Type::String, &Type::Int64]);
        let u0 = Type::Union(vec![&Type::Int64, &Type::String]);

        let t = Type::Union(vec![&t0, &t1]);
        let u = Type::Tuple(vec![&u0, &Type::Int64]);

        assert!(t.is_assignable_to(&u));
        assert!(!u.is_assignable_to(&t));
    }

    #[test]
    fn union_type_equality() {
        // Member types are in the same order.
        let u0 = Type::Union(vec![&Type::Int64, &Type::String]);
        let u1 = Type::Union(vec![&Type::Int64, &Type::String]);
        assert_eq!(u0, u1);

        // Contains the same member types, but in a different order.
        let u0 = Type::Union(vec![&Type::Int64, &Type::String]);
        let u1 = Type::Union(vec![&Type::String, &Type::Int64]);
        assert_ne!(u0, u1); // NOTE: Should we treat these types are equal?
    }

    #[test]
    fn tcx_union() {
        let type_arena = Arena::new();
        let tcx = TypeContext::new(&type_arena);

        // reduce to a type
        let ty = tcx.union([&Type::Int64]);
        assert_eq!(ty, &Type::Int64);
        let ty = tcx.union([&Type::Int64, &Type::Int64]);
        assert_eq!(ty, &Type::Int64);
        let ty = tcx.union([&Type::Int64, &Type::LiteralInt64(1)]);
        assert_eq!(ty, &Type::Int64);

        // union
        let ty = tcx.union([&Type::LiteralInt64(1), &Type::LiteralInt64(2)]);
        assert_eq!(
            ty,
            &Type::Union(vec![&Type::LiteralInt64(1), &Type::LiteralInt64(2)])
        );
    }
}
