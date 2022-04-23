use crate::ty::{expand_union_ty_array, FunctionSignature, Type};

/// Encode type to C struct type name in universal way. "Universal" here means
/// it is independent of runtime environment and machine architecture.
///
/// Types that are represented as the same structure in the C language must
/// return the same string.
///
/// ## 64 bits Integer type
///
/// ```ignore
/// +-----+
/// | "n" |
/// +-----+
/// ```
///
/// ## Integer types
///
/// ```ignore
/// +-----+-------------------------+
/// | "i" | digits (number of bits) |
/// +-----+-------------------------+
/// ```
///
/// ## Tuple type
///
/// ```ignore
/// +-----+---------------------------+---------------+
/// | "T" | digits (number of fields) | (field types) |
/// +-----+---------------------------+---------------+
/// ```
///
/// ## Anonymous struct type
///
/// ```ignore
/// +-----+---------------------------+----------------+
/// | "S" | digits (number of fields) | (named fields) |
/// +-----+---------------------------+----------------+
///
/// named field:
/// +------+-------------------------------------------+------+
/// | type | digits (The length of the following name) | name |
/// +------+-------------------------------------------+------+
///
/// ```
///
/// ## Struct type
///
/// ```ignore
/// +-----+-------+
/// | "S" | name  |
/// +-----+-------+
/// ```
///
/// ## Union type
///
/// ```ignore
/// +-----+---------------------------+---------------+
/// | "U" | digits (number of fields) | (field types) |
/// +-----+---------------------------+---------------+
/// ```
///
/// ## Other types (including literal types)
///
/// NOTE: We don't care a type is literal type or not to make it compatible in
/// C struct type.
///
/// | Type           | Format |
/// | -------------- | ------ |
/// | `boolean`      | `"b"`  |
/// | `string`       | `"s"`  |
/// | `int` (C type) | `"ni"` |
///
pub(crate) fn encode_ty(ty: &Type, buffer: &mut String) {
    match ty {
        Type::Int64 | Type::LiteralInt64(_) => buffer.push('n'),
        Type::Boolean | Type::LiteralBoolean(_) => buffer.push('b'),
        Type::String | Type::LiteralString(_) => buffer.push('s'),
        Type::NativeInt => buffer.push_str("ni"),
        Type::Tuple(fs) => {
            buffer.push('T');
            buffer.push_str(&fs.len().to_string());
            for fty in fs {
                encode_ty(fty, buffer);
            }
        }
        Type::Union(member_types) => {
            let member_types = expand_union_ty_array(member_types);

            buffer.push('U');
            buffer.push_str(&member_types.len().to_string());
            for mty in member_types {
                encode_ty(mty, buffer);
            }
        }
        Type::Struct(struct_ty) => {
            buffer.push('S');
            if let Some(name) = struct_ty.name() {
                buffer.push_str(name);
            } else {
                buffer.push_str(&struct_ty.fields().len().to_string());
                for f in struct_ty.fields() {
                    encode_ty(f.ty(), buffer);
                    buffer.push_str(&f.name().len().to_string());
                    buffer.push_str(f.name());
                }
            }
        }
        Type::Named(named_ty) => {
            encode_ty(named_ty.expect_ty(), buffer);
        }
        Type::Undetermined => unreachable!("untyped code"),
    }
}

/// Function name mangling scheme.
///
/// Types that are treated as different types in this programming language must
/// return separate strings.
///
/// +------+-------------------------------------------+------+-----------------------------+-------------+
/// | "_Z" | digits (The length of the following name) | name | digits (The number of args) | (arg types) |
/// +------+-------------------------------------------+------+-----------------------------+-------------+
///
/// ## Literal types
///
/// To make function overloading work properly, we have to encode literal types.
///
/// ### integers
///
/// +-----+-----+-------------------------+-----+---------+
/// | "L" | "i" | digits (number of bits) | "_" | integer |
/// +-----+-----+-------------------------+-----+---------+
///
/// ### boolean
///
/// +-----+-----+-----------------------+
/// | "L" | "b" | "0": false, "1": true |
/// +-----+-----+-----------------------+
///
/// ### string
///
/// +-----+-----+------------------------------------+-----+-----------------------------------+
/// | "L" | "s" | digits (The length of "b58" field) | "_" | b58 (base58 encoded string value) |
/// +-----+-----+------------------------------------+-----+-----------------------------------+
///
pub(crate) fn mangle_name(signature: &FunctionSignature<'_>) -> String {
    let mut buffer = format!(
        "_Z{}{}{}",
        signature.name().len(),
        signature.name(),
        signature.params().len()
    );

    for p in signature.params() {
        let pty = p.bottom_ty();

        match pty {
            Type::LiteralInt64(n) => {
                buffer.push('L');
                buffer.push('i');
                buffer.push_str("64");
                buffer.push('_');
                buffer.push_str(&n.to_string());
            }
            Type::LiteralBoolean(b) => {
                buffer.push('L');
                buffer.push('b');
                if *b {
                    buffer.push('1');
                } else {
                    buffer.push('0');
                }
            }
            Type::LiteralString(s) => {
                let encoded = bs58::encode(s).into_string();

                buffer.push('L');
                buffer.push('s');

                // Encode literal string with base58 encoding
                buffer.push_str(&encoded.len().to_string());
                buffer.push('_');
                buffer.push_str(&encoded);
            }
            // fall back to encode_ty()
            _ => encode_ty(pty, &mut buffer),
        }
    }

    buffer
}
