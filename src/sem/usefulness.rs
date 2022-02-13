//! Based on usefulness algorithm in Rust:
//! - https://github.com/rust-lang/rust/blob/d331cb710f0/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs
//! - https://github.com/rust-lang/rust/blob/d331cb710f0/compiler/rustc_mir_build/src/thir/pattern/deconstruct_pat.rs
use super::error::SemanticError;
use crate::syntax::token::RangeEnd;
use crate::syntax::{
    CaseArm, Pattern, PatternField, PatternFieldOrSpread, PatternKind, StructPattern,
};
use crate::ty::Type;
use std::{
    cell::Cell,
    cmp::{max, min},
    fmt,
    iter::once,
    ops::RangeInclusive,
};
use typed_arena::Arena;

#[derive(Clone, Copy)]
pub struct MatchCheckContext<'p, 'tcx> {
    pub pattern_arena: &'p Arena<DeconstructedPat<'p, 'tcx>>,
    pub tree_pattern_arena: &'p Arena<Pattern<'p, 'tcx>>,
}

#[derive(Clone, Copy)]
pub struct PatContext<'a, 'p, 'tcx> {
    pub cx: &'a MatchCheckContext<'p, 'tcx>,
    /// Type of the current column under investigation.
    pub ty: &'tcx Type<'tcx>,
    /// Whether the current pattern is the whole pattern as found in a match arm, or if it's a
    /// subpattern.
    pub(super) is_top_level: bool,
    /// Wether the current pattern is from a `non_exhaustive` enum.
    pub(super) is_non_exhaustive: bool,
}

/// An inclusive interval, used for precise integer exhaustiveness checking.
/// `IntRange`s always store a contiguous range. This means that values are
/// encoded such that `0` encodes the minimum value for the integer,
/// regardless of the signedness.
/// For example, the pattern `-128..=127i8` is encoded as `0..=255`.
/// This makes comparisons and arithmetic on interval endpoints much more
/// straightforward. See `signed_bias` for details.
///
/// `IntRange` is never used to encode an empty range or a "range" that wraps
/// around the (offset) space: i.e., `range.lo <= range.hi`.
#[derive(Clone, PartialEq, Eq)]
pub struct IntRange {
    range: RangeInclusive<u128>,
    /// Keeps the bias used for encoding the range. It depends on the type of the range and
    /// possibly the pointer size of the current architecture. The algorithm ensures we never
    /// compare `IntRange`s with different types/architectures.
    bias: i128,
}

impl IntRange {
    #[inline]
    fn is_integral(ty: &Type) -> bool {
        matches!(ty, Type::Int64 | Type::Boolean)
    }

    // The return value of `signed_bias` should be XORed with an endpoint to encode/decode it.
    fn signed_bias(ty: &Type) -> i128 {
        match ty {
            Type::Int64 => 1i128 << (i64::BITS as i128 - 1),
            Type::Boolean => 0,
            _ => 0,
        }
    }

    #[inline]
    fn encode_value(value: i64, bias: i128) -> u128 {
        u128::try_from(i128::try_from(value).unwrap() + bias).unwrap()
    }

    #[inline]
    fn decode_value(value: u128, bias: i128) -> i64 {
        i64::try_from(i128::try_from(value).unwrap() - bias).unwrap()
    }

    fn from_const(value: i64, ty: &Type) -> IntRange {
        let bias = Self::signed_bias(ty);
        let val = Self::encode_value(value, bias);

        IntRange {
            range: val..=val,
            bias,
        }
    }

    fn from_i64(value: i64) -> IntRange {
        Self::from_const(value, &Type::Int64)
    }

    fn from_bool(value: bool) -> IntRange {
        Self::from_const(i64::try_from(value).unwrap(), &Type::Boolean)
    }

    #[inline]
    fn from_range(lo: i64, hi: i64, ty: &Type, end: RangeEnd) -> IntRange {
        let bias = IntRange::signed_bias(ty);
        let lo = Self::encode_value(lo, bias);
        let hi = Self::encode_value(hi, bias);

        let offset = (end == RangeEnd::Excluded) as u128;
        if lo > hi || (lo == hi && end == RangeEnd::Excluded) {
            // This should have been caught earlier by E0030.
            unreachable!("malformed range pattern: {}..={}", lo, (hi - offset));
        }
        IntRange {
            range: lo..=(hi - offset),
            bias,
        }
    }

    fn is_singleton(&self) -> bool {
        self.range.start() == self.range.end()
    }

    fn boundaries(&self) -> (u128, u128) {
        (*self.range.start(), *self.range.end())
    }

    fn is_subrange(&self, other: &Self) -> bool {
        other.range.start() <= self.range.start() && self.range.end() <= other.range.end()
    }

    fn intersection(&self, other: &Self) -> Option<Self> {
        let (lo, hi) = self.boundaries();
        let (other_lo, other_hi) = other.boundaries();
        if lo <= other_hi && other_lo <= hi {
            Some(IntRange {
                range: max(lo, other_lo)..=min(hi, other_hi),
                bias: self.bias,
            })
        } else {
            None
        }
    }

    /// Only used for displaying the range properly.
    fn to_pat<'tcx>(&self, ty: &'tcx Type<'tcx>) -> Pattern<'tcx, 'tcx> {
        let (lo, hi) = self.boundaries();

        let lo = Self::decode_value(lo, self.bias);
        let hi = Self::decode_value(hi, self.bias);

        let kind = if lo == hi {
            match ty {
                Type::Int64 => PatternKind::Integer(lo),
                Type::Boolean => PatternKind::Boolean(lo != 0),
                _ => unreachable!("unexpected type ({}) for int range", ty),
            }
        } else {
            PatternKind::Range {
                lo,
                hi,
                end: RangeEnd::Included,
            }
        };

        Pattern::new(kind)
    }

    /// See `Constructor::is_covered_by`
    fn is_covered_by(&self, other: &Self) -> bool {
        if self.intersection(other).is_some() {
            // Constructor splitting should ensure that all intersections we encounter are actually
            // inclusions.
            assert!(self.is_subrange(other));
            true
        } else {
            false
        }
    }
}

/// Note: this is often not what we want: e.g. `false` is converted into the range `0..=0` and
/// would be displayed as such. To render properly, convert to a pattern first.
impl fmt::Debug for IntRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (lo, hi) = self.boundaries();
        let lo = Self::decode_value(lo, self.bias);
        let hi = Self::decode_value(hi, self.bias);

        write!(f, "{}", lo)?;
        write!(f, "{}", RangeEnd::Included)?;
        write!(f, "{}", hi)
    }
}

/// Represents a border between 2 integers. Because the intervals spanning borders must be able to
/// cover every integer, we need to be able to represent 2^128 + 1 such borders.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum IntBorder {
    JustBefore(u128),
    AfterMax,
}

/// A range of integers that is partitioned into disjoint subranges. This does constructor
/// splitting for integer ranges as explained at the top of the file.
///
/// This is fed multiple ranges, and returns an output that covers the input, but is split so that
/// the only intersections between an output range and a seen range are inclusions. No output range
/// straddles the boundary of one of the inputs.
///
/// The following input:
/// ```ignore
///   |-------------------------| // `self`
/// |------|  |----------|   |----|
///    |-------| |-------|
/// ```
/// would be iterated over as follows:
/// ```ignore
///   ||---|--||-|---|---|---|--|
/// ```

#[derive(Debug, Clone)]
struct SplitIntRange {
    /// The range we are splitting
    range: IntRange,
    /// The borders of ranges we have seen. They are all contained within `range`. This is kept
    /// sorted.
    borders: Vec<IntBorder>,
}

impl SplitIntRange {
    fn new(range: IntRange) -> Self {
        SplitIntRange {
            range,
            borders: Vec::new(),
        }
    }

    /// Internal use
    fn to_borders(r: IntRange) -> [IntBorder; 2] {
        use IntBorder::*;
        let (lo, hi) = r.boundaries();
        let lo = JustBefore(lo);
        let hi = match hi.checked_add(1) {
            Some(m) => JustBefore(m),
            None => AfterMax,
        };
        [lo, hi]
    }

    /// Add ranges relative to which we split.
    fn split(&mut self, ranges: impl Iterator<Item = IntRange>) {
        let this_range = &self.range;
        let included_ranges = ranges.filter_map(|r| this_range.intersection(&r));
        let included_borders = included_ranges.flat_map(|r| {
            let borders = Self::to_borders(r);
            once(borders[0]).chain(once(borders[1]))
        });
        self.borders.extend(included_borders);
        self.borders.sort_unstable();
    }

    /// Iterate over the contained ranges.
    fn iter(&self) -> impl Iterator<Item = IntRange> + '_ {
        use IntBorder::*;

        let self_range = Self::to_borders(self.range.clone());
        // Start with the start of the range.
        let mut prev_border = self_range[0];
        self.borders
            .iter()
            .copied()
            // End with the end of the range.
            .chain(once(self_range[1]))
            // List pairs of adjacent borders.
            .map(move |border| {
                let ret = (prev_border, border);
                prev_border = border;
                ret
            })
            // Skip duplicates.
            .filter(|(prev_border, border)| prev_border != border)
            // Finally, convert to ranges.
            .map(move |(prev_border, border)| {
                let range = match (prev_border, border) {
                    (JustBefore(n), JustBefore(m)) if n < m => n..=(m - 1),
                    (JustBefore(n), AfterMax) => n..=u128::MAX,
                    _ => unreachable!(), // Ruled out by the sorting and filtering we did
                };
                IntRange {
                    range,
                    bias: self.range.bias,
                }
            })
    }
}

/// A wildcard constructor that we split relative to the constructors in the matrix, as explained
/// at the top of the file.
///
/// A constructor that is not present in the matrix rows will only be covered by the rows that have
/// wildcards. Thus we can group all of those constructors together; we call them "missing
/// constructors". Splitting a wildcard would therefore list all present constructors individually
/// (or grouped if they are integers or slices), and then all missing constructors together as a
/// group.
///
/// However we can go further: since any constructor will match the wildcard rows, and having more
/// rows can only reduce the amount of usefulness witnesses, we can skip the present constructors
/// and only try the missing ones.
/// This will not preserve the whole list of witnesses, but will preserve whether the list is empty
/// or not. In fact this is quite natural from the point of view of diagnostics too. This is done
/// in `to_ctors`: in some cases we only return `Missing`.

#[derive(Debug)]
pub(super) struct SplitWildcard {
    /// Constructors seen in the matrix.
    matrix_ctors: Vec<Constructor>,
    /// All the constructors for this type
    all_ctors: Vec<Constructor>,
}

impl<'tcx> SplitWildcard {
    pub(super) fn new(pcx: PatContext) -> Self {
        let all_ctors = match pcx.ty {
            Type::Int64 => {
                let ctor = Constructor::IntRange(IntRange::from_range(
                    i64::MIN,
                    i64::MAX,
                    &Type::Int64,
                    RangeEnd::Included,
                ));
                vec![ctor]
            }
            Type::Boolean => {
                let ctor = Constructor::IntRange(IntRange::from_range(
                    0,
                    1,
                    &Type::Boolean,
                    RangeEnd::Included,
                ));
                vec![ctor]
            }
            Type::Tuple(_) | Type::Struct(_) => vec![Constructor::Single],
            // This type is one for which we cannot list constructors, like `str` or `f64`.
            Type::String | Type::Named(_) | Type::Undetermined => vec![Constructor::NonExhaustive],
            // A constant string
            Type::LiteralString(s) => vec![Constructor::Str(s.clone())],
            Type::NativeInt => unreachable!("Native C types are not supported."),
        };

        SplitWildcard {
            matrix_ctors: Vec::new(),
            all_ctors,
        }
    }

    /// Pass a set of constructors relative to which to split this one. Don't call twice, it won't
    /// do what you want.
    pub fn split<'a>(
        &mut self,
        pcx: PatContext<'_, '_, 'tcx>,
        ctors: impl Iterator<Item = &'a Constructor> + Clone,
    ) {
        // Since `all_ctors` never contains wildcards, this won't recurse further.
        self.all_ctors = self
            .all_ctors
            .iter()
            .flat_map(|ctor| ctor.split(pcx, ctors.clone()))
            .collect();
        self.matrix_ctors = ctors.filter(|c| !c.is_wildcard()).cloned().collect();
    }

    /// Whether there are any value constructors for this type that are not present in the matrix.
    fn any_missing(&self, pcx: PatContext<'_, '_, 'tcx>) -> bool {
        self.iter_missing(pcx).next().is_some()
    }

    /// Iterate over the constructors for this type that are not present in the matrix.
    pub fn iter_missing<'a, 'p>(
        &'a self,
        _pcx: PatContext<'a, 'p, 'tcx>,
    ) -> impl Iterator<Item = &'a Constructor> {
        self.all_ctors
            .iter()
            .filter(|ctor| !ctor.is_covered_by_any(&self.matrix_ctors))
    }

    /// Return the set of constructors resulting from splitting the wildcard. As explained at the
    /// top of the file, if any constructors are missing we can ignore the present ones.
    fn into_ctors(self, pcx: PatContext<'_, '_, 'tcx>) -> Vec<Constructor> {
        if self.any_missing(pcx) {
            // Some constructors are missing, thus we can specialize with the special `Missing`
            // constructor, which stands for those constructors that are not seen in the matrix,
            // and matches the same rows as any of them (namely the wildcard rows). See the top of
            // the file for details.
            // However, when all constructors are missing we can also specialize with the full
            // `Wildcard` constructor. The difference will depend on what we want in diagnostics.

            // If some constructors are missing, we typically want to report those constructors,
            // e.g.:
            // ```
            //     enum Direction { N, S, E, W }
            //     let Direction::N = ...;
            // ```
            // we can report 3 witnesses: `S`, `E`, and `W`.
            //
            // However, if the user didn't actually specify a constructor
            // in this arm, e.g., in
            // ```
            //     let x: (Direction, Direction, bool) = ...;
            //     let (_, _, false) = x;
            // ```
            // we don't want to show all 16 possible witnesses `(<direction-1>, <direction-2>,
            // true)` - we are satisfied with `(_, _, true)`. So if all constructors are missing we
            // prefer to report just a wildcard `_`.
            //
            // The exception is: if we are at the top-level, for example in an empty match, we
            // sometimes prefer reporting the list of constructors instead of just `_`.
            let report_when_all_missing = pcx.is_top_level && !IntRange::is_integral(pcx.ty);
            let ctor = if !self.matrix_ctors.is_empty() || report_when_all_missing {
                if pcx.is_non_exhaustive {
                    Constructor::Missing {
                        nonexhaustive_enum_missing_real_variants: self
                            .iter_missing(pcx)
                            .any(|c| !(c.is_non_exhaustive() || c.is_unstable_variant(pcx))),
                    }
                } else {
                    Constructor::Missing {
                        nonexhaustive_enum_missing_real_variants: false,
                    }
                }
            } else {
                Constructor::Wildcard
            };
            return vec![ctor];
        }

        // All the constructors are present in the matrix, so we just go through them all.
        self.all_ctors
    }
}

/// A row of a matrix. Rows of len 1 are very common, which is why `SmallVec[_; 2]`
/// works well.
#[derive(Clone)]
struct PatStack<'p, 'tcx> {
    pats: Vec<&'p DeconstructedPat<'p, 'tcx>>,
}

impl<'p, 'tcx> PatStack<'p, 'tcx> {
    fn from_pattern(pat: &'p DeconstructedPat<'p, 'tcx>) -> Self {
        Self::from_vec(vec![pat])
    }

    fn from_vec(vec: Vec<&'p DeconstructedPat<'p, 'tcx>>) -> Self {
        PatStack { pats: vec }
    }

    fn is_empty(&self) -> bool {
        self.pats.is_empty()
    }

    fn len(&self) -> usize {
        self.pats.len()
    }

    fn head(&self) -> &'p DeconstructedPat<'p, 'tcx> {
        self.pats[0]
    }

    fn iter(&self) -> impl Iterator<Item = &DeconstructedPat<'p, 'tcx>> {
        self.pats.iter().copied()
    }

    // Recursively expand the first pattern into its subpatterns. Only useful if the pattern is an
    // or-pattern. Panics if `self` is empty.
    fn expand_or_pat<'a>(&'a self) -> impl Iterator<Item = PatStack<'p, 'tcx>> + 'a {
        self.head().iter_fields().map(move |pat| {
            let mut new_patstack = PatStack::from_pattern(pat);

            new_patstack.pats.extend_from_slice(&self.pats[1..]);
            new_patstack
        })
    }

    /// This computes `S(self.head().ctor(), self)`. See top of the file for explanations.
    ///
    /// Structure patterns with a partial wild pattern (Foo { a: 42, .. }) have their missing
    /// fields filled with wild patterns.
    ///
    /// This is roughly the inverse of `Constructor::apply`.
    fn pop_head_constructor(
        &self,
        cx: &MatchCheckContext<'p, 'tcx>,
        ctor: &Constructor,
    ) -> PatStack<'p, 'tcx> {
        // We pop the head pattern and push the new fields extracted from the arguments of
        // `self.head()`.
        let mut new_fields = self.head().specialize(cx, ctor);
        new_fields.extend_from_slice(&self.pats[1..]);
        PatStack::from_vec(new_fields)
    }
}

/// A 2D matrix.
#[derive(Clone)]
pub(super) struct Matrix<'p, 'tcx> {
    patterns: Vec<PatStack<'p, 'tcx>>,
}

impl<'p, 'tcx> Matrix<'p, 'tcx> {
    fn empty() -> Self {
        Matrix { patterns: vec![] }
    }

    /// Pushes a new row to the matrix. If the row starts with an or-pattern, this recursively
    /// expands it.
    fn push(&mut self, row: PatStack<'p, 'tcx>) {
        if !row.is_empty() && row.head().is_or_pat() {
            self.patterns.extend(row.expand_or_pat());
        } else {
            self.patterns.push(row);
        }
    }

    /// Iterate over the first component of each row
    fn heads<'a>(&'a self) -> impl Iterator<Item = &'p DeconstructedPat<'p, 'tcx>> + Clone + 'a {
        self.patterns.iter().map(|r| r.head())
    }

    /// This computes `S(constructor, self)`. See top of the file for explanations.
    fn specialize_constructor(
        &self,
        pcx: PatContext<'_, 'p, 'tcx>,
        ctor: &Constructor,
    ) -> Matrix<'p, 'tcx> {
        let mut matrix = Matrix::empty();
        for row in &self.patterns {
            if ctor.is_covered_by(pcx, row.head().ctor()) {
                let new_row = row.pop_head_constructor(pcx.cx, ctor);
                matrix.push(new_row);
            }
        }
        matrix
    }
}

/// Pretty-printer for matrices of patterns, example:
///
/// ```text
/// + _     + []                +
/// + true  + [First]           +
/// + true  + [Second(true)]    +
/// + false + [_]               +
/// + _     + [_, _, tail @ ..] +
/// ```
impl<'p, 'tcx> fmt::Debug for Matrix<'p, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;

        let Matrix { patterns: m, .. } = self;
        let pretty_printed_matrix: Vec<Vec<String>> = m
            .iter()
            .map(|row| row.iter().map(|pat| format!("{:?}", pat)).collect())
            .collect();

        let column_count = m.iter().map(|row| row.len()).next().unwrap_or(0);
        assert!(m.iter().all(|row| row.len() == column_count));
        let column_widths: Vec<usize> = (0..column_count)
            .map(|col| {
                pretty_printed_matrix
                    .iter()
                    .map(|row| row[col].len())
                    .max()
                    .unwrap_or(0)
            })
            .collect();

        for row in pretty_printed_matrix {
            write!(f, "+")?;
            for (column, pat_str) in row.into_iter().enumerate() {
                write!(f, " ")?;
                write!(f, "{:1$}", pat_str, column_widths[column])?;
                write!(f, " +")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

/// Pretty-printing for matrix row.
impl<'p, 'tcx> fmt::Debug for PatStack<'p, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "+")?;
        for pat in self.iter() {
            write!(f, " {:?} +", pat)?;
        }
        Ok(())
    }
}

/// A value can be decomposed into a constructor applied to some fields. This struct represents
/// the constructor. See also `Fields`.
///
/// `pat_constructor` retrieves the constructor corresponding to a pattern.
/// `specialize_constructor` returns the list of fields corresponding to a pattern, given a
/// constructor. `Constructor::apply` reconstructs the pattern from a pair of `Constructor` and
/// `Fields`.

#[derive(Clone, Debug, PartialEq)]
pub enum Constructor {
    /// The constructor for patterns that have a single constructor, like tuples, struct patterns
    /// and fixed-length arrays.
    Single,
    /// Ranges of integer literal values (`2`, `2..=5` or `2..5`).
    IntRange(IntRange),
    /// String constant
    Str(String),
    /// Fake extra constructor for enums that aren't allowed to be matched exhaustively. Also used
    /// for those types for which we cannot list constructors explicitly, like `f64` and `str`.
    NonExhaustive,
    /// Stands for constructors that are not seen in the matrix, as explained in the documentation
    /// for [`SplitWildcard`]. The carried `bool` is used for the `non_exhaustive_omitted_patterns`
    /// lint.
    Missing {
        nonexhaustive_enum_missing_real_variants: bool,
    },
    /// Wildcard pattern.
    Wildcard,
    /// Or-pattern.
    Or,
}

impl<'tcx> Constructor {
    pub(super) fn is_wildcard(&self) -> bool {
        matches!(self, Self::Wildcard)
    }

    fn as_int_range(&self) -> Option<&IntRange> {
        match self {
            Self::IntRange(range) => Some(range),
            _ => None,
        }
    }

    pub(super) fn is_non_exhaustive(&self) -> bool {
        matches!(self, Self::NonExhaustive)
    }

    /// Checks if the `Constructor` is a variant and `TyCtxt::eval_stability` returns
    /// `EvalResult::Deny { .. }`.
    ///
    /// This means that the variant has a stdlib unstable feature marking it.
    pub fn is_unstable_variant(&self, _pcx: PatContext<'_, '_, 'tcx>) -> bool {
        false
    }

    /// The number of fields for this constructor. This must be kept in sync with
    /// `Fields::wildcards`.
    pub fn arity(&self, pcx: PatContext<'_, '_, 'tcx>) -> usize {
        match self {
            Self::Single => match pcx.ty {
                Type::Tuple(fs) => fs.len(),
                Type::Struct(struct_ty) => struct_ty.fields().len(),
                _ => unreachable!("Unexpected type for `Single` constructor: {:?}", pcx.ty),
            },
            Self::Wildcard
            | Self::IntRange(_)
            | Self::Str(_)
            | Self::NonExhaustive
            | Self::Missing { .. } => 0,
            Self::Or => unreachable!("The `Or` constructor doesn't have a fixed arity"),
        }
    }

    /// Returns whether `self` is covered by `other`, i.e. whether `self` is a subset of `other`.
    /// For the simple cases, this is simply checking for equality. For the "grouped" constructors,
    /// this checks for inclusion.
    // We inline because this has a single call site in `Matrix::specialize_constructor`.
    pub fn is_covered_by<'p>(&self, _pcx: PatContext<'_, 'p, 'tcx>, other: &Self) -> bool {
        // This must be kept in sync with `is_covered_by_any`.
        match (self, other) {
            // Wildcards cover anything
            (_, Self::Wildcard) => true,
            // The missing ctors are not covered by anything in the matrix except wildcards.
            (Self::Missing { .. } | Self::Wildcard, _) => false,
            (Self::Single, Self::Single) => true,
            (Self::IntRange(self_range), Self::IntRange(other_range)) => {
                self_range.is_covered_by(other_range)
            }
            (Self::Str(self_val), Self::Str(other_val)) => self_val == other_val,
            // Only a wildcard pattern can match the special extra constructor.
            (Self::NonExhaustive, _) => false,
            _ => unreachable!(
                "trying to compare incompatible constructors {:?} and {:?}",
                self, other
            ),
        }
    }

    /// Faster version of `is_covered_by` when applied to many constructors. `used_ctors` is
    /// assumed to be built from `matrix.head_ctors()` with wildcards filtered out, and `self` is
    /// assumed to have been split from a wildcard.
    fn is_covered_by_any(&self, used_ctors: &[Constructor]) -> bool {
        if used_ctors.is_empty() {
            return false;
        }

        // This must be kept in sync with `is_covered_by`.
        match self {
            // If `self` is `Single`, `used_ctors` cannot contain anything else than `Single`s.
            Self::Single => !used_ctors.is_empty(),
            Self::IntRange(range) => used_ctors
                .iter()
                .filter_map(|c| c.as_int_range())
                .any(|other| range.is_covered_by(other)),
            // This constructor is never covered by anything else
            Self::NonExhaustive => false,
            Self::Str(..) | Self::Wildcard | Self::Missing { .. } | Self::Or => {
                unreachable!("found unexpected ctor in all_ctors: {:?}", self)
            }
        }
    }

    /// Some constructors (namely `Wildcard`, `IntRange` and `Slice`) actually stand for a set of actual
    /// constructors (like variants, integers or fixed-sized slices). When specializing for these
    /// constructors, we want to be specialising for the actual underlying constructors.
    /// Naively, we would simply return the list of constructors they correspond to. We instead are
    /// more clever: if there are constructors that we know will behave the same wrt the current
    /// matrix, we keep them grouped. For example, all slices of a sufficiently large length
    /// will either be all useful or all non-useful with a given matrix.
    ///
    /// See the branches for details on how the splitting is done.
    ///
    /// This function may discard some irrelevant constructors if this preserves behavior and
    /// diagnostics. Eg. for the `_` case, we ignore the constructors already present in the
    /// matrix, unless all of them are.
    pub(super) fn split<'a>(
        &self,
        pcx: PatContext<'_, '_, 'tcx>,
        ctors: impl Iterator<Item = &'a Constructor> + Clone,
    ) -> Vec<Self> {
        match self {
            Constructor::Wildcard => {
                let mut split_wildcard = SplitWildcard::new(pcx);
                split_wildcard.split(pcx, ctors);
                split_wildcard.into_ctors(pcx)
            }
            // Fast-track if the range is trivial. In particular, we don't do the overlapping
            // ranges check.
            Constructor::IntRange(ctor_range) if !ctor_range.is_singleton() => {
                let mut split_range = SplitIntRange::new(ctor_range.clone());
                let int_ranges = ctors.filter_map(|ctor| ctor.as_int_range());
                split_range.split(int_ranges.cloned());
                split_range.iter().map(Constructor::IntRange).collect()
            }
            // Any other constructor can be used unchanged.
            _ => vec![self.clone()],
        }
    }
}

/// A value can be decomposed into a constructor applied to some fields. This struct represents
/// those fields, generalized to allow patterns in each field. See also `Constructor`.
///
/// This is constructed for a constructor using [`Fields::wildcards()`]. The idea is that
/// [`Fields::wildcards()`] constructs a list of fields where all entries are wildcards, and then
/// given a pattern we fill some of the fields with its subpatterns.
/// In the following example `Fields::wildcards` returns `[_, _, _, _]`. Then in
/// `extract_pattern_arguments` we fill some of the entries, and the result is
/// `[Some(0), _, _, _]`.
/// ```ignore
/// let x: [Option<u8>; 4] = foo();
/// match x {
///     [Some(0), ..] => {}
/// }
/// ```
///
/// Note that the number of fields of a constructor may not match the fields declared in the
/// original struct/variant. This happens if a private or `non_exhaustive` field is uninhabited,
/// because the code mustn't observe that it is uninhabited. In that case that field is not
/// included in `fields`. For that reason, when you have a `mir::Field` you must use
/// `index_with_declared_idx`.
#[derive(Debug, Clone, Copy)]
pub struct Fields<'p, 'tcx> {
    fields: &'p [DeconstructedPat<'p, 'tcx>],
}

impl<'p, 'tcx> Fields<'p, 'tcx> {
    fn empty() -> Self {
        Fields { fields: &[] }
    }

    pub fn from_iter(
        cx: &MatchCheckContext<'p, 'tcx>,
        fields: impl IntoIterator<Item = DeconstructedPat<'p, 'tcx>>,
    ) -> Self {
        // Prevent the function from being called recursively. The arena
        // allocator can't be invoked recursively.
        let vs = fields.into_iter().collect::<Vec<_>>();
        let fields: &[_] = cx.pattern_arena.alloc_extend(vs);

        Fields { fields }
    }

    fn wildcards_from_tys(
        cx: &MatchCheckContext<'p, 'tcx>,
        tys: impl IntoIterator<Item = &'tcx Type<'tcx>>,
    ) -> Self {
        Fields::from_iter(cx, tys.into_iter().map(DeconstructedPat::wildcard))
    }

    /// Creates a new list of wildcard fields for a given constructor. The result must have a
    /// length of `constructor.arity()`.
    pub fn wildcards(
        cx: &MatchCheckContext<'p, 'tcx>,
        ty: &'tcx Type<'tcx>,
        constructor: &Constructor,
    ) -> Self {
        match constructor {
            Constructor::Single => match ty.bottom_ty() {
                Type::Tuple(fs) => Fields::wildcards_from_tys(cx, fs.iter().copied()),
                Type::Struct(struct_ty) => Fields::wildcards_from_tys(
                    cx,
                    struct_ty.fields().iter().map(|f| f.ty().bottom_ty()),
                ),
                ty => unreachable!("Unexpected type for `Single` constructor: {:?}", ty),
            },
            Constructor::IntRange(..)
            | Constructor::Str(..)
            | Constructor::NonExhaustive
            | Constructor::Wildcard
            | Constructor::Missing { .. } => Fields::empty(),
            Constructor::Or => unreachable!("called `Fields::wildcards` on an `Or` ctor"),
        }
    }

    /// Returns the list of patterns.
    pub fn iter_patterns<'a>(
        &'a self,
    ) -> impl Iterator<Item = &'p DeconstructedPat<'p, 'tcx>> + 'a {
        self.fields.iter()
    }
}

/// Values and patterns can be represented as a constructor applied to some fields. This represents
/// a pattern in this form.
/// This also keeps track of whether the pattern has been found reachable during analysis. For this
/// reason we should be careful not to clone patterns for which we care about that. Use
/// `clone_and_forget_reachability` if you're sure.
#[derive(Debug, Clone)]

pub struct DeconstructedPat<'p, 'tcx> {
    ctor: Constructor,
    fields: Fields<'p, 'tcx>,
    ty: &'tcx Type<'tcx>,
    reachable: Cell<bool>,
}

impl<'p, 'tcx> DeconstructedPat<'p, 'tcx> {
    pub(super) fn wildcard(ty: &'tcx Type<'tcx>) -> Self {
        Self::new(Constructor::Wildcard, Fields::empty(), ty)
    }

    pub(super) fn new(ctor: Constructor, fields: Fields<'p, 'tcx>, ty: &'tcx Type<'tcx>) -> Self {
        DeconstructedPat {
            ctor,
            fields,
            ty: ty.bottom_ty(),
            reachable: Cell::new(false),
        }
    }

    /// Construct a pattern that matches everything that starts with this constructor.
    /// For example, if `ctor` is a `Constructor::Variant` for `Option::Some`, we get the pattern
    /// `Some(_)`.
    pub fn wild_from_ctor(pcx: PatContext<'_, 'p, 'tcx>, ctor: Constructor) -> Self {
        let fields = Fields::wildcards(pcx.cx, pcx.ty, &ctor);
        DeconstructedPat::new(ctor, fields, pcx.ty)
    }

    /// Clone this value. This method emphasizes that cloning loses reachability information and
    /// should be done carefully.
    pub fn clone_and_forget_reachability(&self) -> Self {
        DeconstructedPat::new(self.ctor.clone(), self.fields, self.ty)
    }

    pub fn from_pat(cx: &MatchCheckContext<'p, 'tcx>, pat: &Pattern<'_, 'tcx>) -> Self {
        let pat_ty = pat.expect_ty().bottom_ty();

        let ctor;
        let fields;
        match pat.kind() {
            PatternKind::Var(_) | PatternKind::Wildcard => {
                ctor = Constructor::Wildcard;
                fields = Fields::empty();
            }
            PatternKind::Integer(value) => {
                let int_range = IntRange::from_i64(*value);

                ctor = Constructor::IntRange(int_range);
                fields = Fields::empty();
            }
            PatternKind::Boolean(b) => {
                let int_range = IntRange::from_bool(*b);

                ctor = Constructor::IntRange(int_range);
                fields = Fields::empty();
            }
            PatternKind::Range { lo, hi, end } => {
                let int_range = IntRange::from_range(*lo, *hi, pat_ty, *end);

                ctor = Constructor::IntRange(int_range);
                fields = Fields::empty();
            }
            PatternKind::String(s) => {
                ctor = Constructor::Str(s.clone());
                fields = Fields::empty();
            }
            PatternKind::Tuple(sub_pats) => {
                ctor = Constructor::Single;
                let pats: Vec<_> = sub_pats
                    .iter()
                    .map(|pat| DeconstructedPat::from_pat(cx, pat))
                    .collect();

                fields = Fields::from_iter(cx, pats);
            }
            PatternKind::Struct(struct_pat) => {
                ctor = Constructor::Single;

                // Convert struct fields to deconstruct patterns.
                // We must follow the order of fields in the type.
                let struct_ty = if let Type::Struct(struct_ty) = pat_ty {
                    struct_ty
                } else {
                    unreachable!("Pattern type {} must be struct type.", pat_ty);
                };

                let mut sub_pats = vec![];

                for f in struct_ty.fields() {
                    let sub_pat = if let Some(pat_field) = struct_pat.get_field(f.name()) {
                        DeconstructedPat::from_pat(cx, pat_field.pattern())
                    } else {
                        // omitted fields are handled by wildcard
                        DeconstructedPat::wildcard(f.ty())
                    };

                    sub_pats.push(sub_pat);
                }

                fields = Fields::from_iter(cx, sub_pats);
            }
            PatternKind::Or(..) => {
                ctor = Constructor::Or;
                let pats = expand_or_pat(pat)
                    .into_iter()
                    .map(|pat| DeconstructedPat::from_pat(cx, pat));
                fields = Fields::from_iter(cx, pats);
            }
        }

        DeconstructedPat::new(ctor, fields, pat_ty)
    }

    // Only used for error description
    pub fn to_pat(&self, cx: &MatchCheckContext<'p, 'tcx>) -> &'p Pattern<'p, 'tcx> {
        let kind = match &self.ctor {
            Constructor::Single => match self.ty() {
                Type::Tuple(_) => {
                    let sub_patterns = self.iter_fields().map(|p| p.to_pat(cx));
                    PatternKind::Tuple(sub_patterns.collect())
                }
                Type::Struct(struct_ty) => {
                    let fields: Vec<_> = self.iter_fields().collect();

                    assert!(fields.len() == struct_ty.fields().len());

                    let pat_fields: Vec<_> = fields
                        .iter()
                        .zip(struct_ty.fields())
                        .map(|(pat, f)| PatternField::new(f.name().to_string(), pat.to_pat(cx)))
                        .map(PatternFieldOrSpread::PatternField)
                        .collect();

                    if let Some(name) = struct_ty.name() {
                        PatternKind::Struct(StructPattern::new(Some(name.to_string()), pat_fields))
                    } else {
                        PatternKind::Struct(StructPattern::new(None, pat_fields))
                    }
                }
                _ => unreachable!("unexpected ctor for type {:?} {:?}", self.ctor, self.ty),
            },
            Constructor::IntRange(range) => {
                let pat = range.to_pat(self.ty());
                return cx.tree_pattern_arena.alloc(pat);
            }
            Constructor::Str(s) => PatternKind::String(s.clone()),
            Constructor::Wildcard | Constructor::NonExhaustive => PatternKind::Wildcard,
            Constructor::Missing { .. } => unreachable!(
                "trying to convert a `Missing` constructor into a `Pat`; this is probably a bug,
                `Missing` should have been processed in `apply_constructors`"
            ),
            Constructor::Or => unreachable!("can't convert to pattern: {:?}", self),
        };

        let pat = Pattern::new(kind);
        pat.assign_ty(self.ty());
        cx.tree_pattern_arena.alloc(pat)
    }

    pub(super) fn ctor(&self) -> &Constructor {
        &self.ctor
    }

    pub(super) fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }

    pub fn iter_fields<'a>(&'a self) -> impl Iterator<Item = &'p DeconstructedPat<'p, 'tcx>> + 'a {
        self.fields.iter_patterns()
    }

    pub fn is_or_pat(&self) -> bool {
        matches!(self.ctor, Constructor::Or)
    }

    /// Specialize this pattern with a constructor.
    /// `other_ctor` can be different from `self.ctor`, but must be covered by it.
    pub fn specialize<'a>(
        &'a self,
        cx: &MatchCheckContext<'p, 'tcx>,
        other_ctor: &Constructor,
    ) -> Vec<&'p DeconstructedPat<'p, 'tcx>> {
        match (&self.ctor, other_ctor) {
            (Constructor::Wildcard, _) => {
                // We return a wildcard for each field of `other_ctor`.
                Fields::wildcards(cx, self.ty, other_ctor)
                    .iter_patterns()
                    .collect()
            }
            _ => self.fields.iter_patterns().collect(),
        }
    }

    /// We keep track for each pattern if it was ever reachable during the analysis. This is used
    /// with `unreachable_spans` to report unreachable subpatterns arising from or patterns.
    pub fn set_reachable(&self) {
        self.reachable.set(true)
    }

    pub fn is_reachable(&self) -> bool {
        self.reachable.get()
    }

    /// Report the spans of subpatterns that were not reachable, if any.
    pub fn unreachable_sub_pats(
        &self,
        cx: &MatchCheckContext<'p, 'tcx>,
    ) -> Vec<&'p Pattern<'p, 'tcx>> {
        let mut sub_pats = Vec::new();
        self.collect_unreachable_spans(cx, &mut sub_pats);
        sub_pats
    }

    fn collect_unreachable_spans(
        &self,
        cx: &MatchCheckContext<'p, 'tcx>,
        sub_pats: &mut Vec<&'p Pattern<'p, 'tcx>>,
    ) {
        // We don't look at subpatterns if we already reported the whole pattern as unreachable.
        if !self.is_reachable() {
            sub_pats.push(self.to_pat(cx));
        } else {
            for p in self.iter_fields() {
                p.collect_unreachable_spans(cx, sub_pats);
            }
        }
    }
}

/// The arm of a match expression.
#[derive(Debug, Clone, Copy)]
pub struct MatchArm<'p, 'tcx> {
    /// The pattern must have been lowered through `check_match::MatchVisitor::lower_pattern`.
    pub pat: &'p DeconstructedPat<'p, 'tcx>,
    pub has_guard: bool,
}

/// Indicates whether or not a given arm is reachable.
#[derive(Debug, Clone)]

pub enum Reachability<'p, 'tcx> {
    /// The arm is reachable.
    Reachable {
        unreachable_sub_patterns: Vec<&'p Pattern<'p, 'tcx>>,
    },
    /// The arm is unreachable.
    Unreachable,
}

/// The output of checking a match for exhaustiveness and arm reachability.

pub struct UsefulnessReport<'p, 'tcx> {
    /// For each arm of the input, whether that arm is reachable after the arms above it.
    pub arm_usefulness: Vec<(MatchArm<'p, 'tcx>, Reachability<'p, 'tcx>)>,
    /// If the match is exhaustive, this is empty. If not, this contains witnesses for the lack of
    /// exhaustiveness.
    pub non_exhaustiveness_witnesses: Vec<DeconstructedPat<'p, 'tcx>>,
}

/// This carries the results of computing usefulness, as described at the top of the file. When
/// checking usefulness of a match branch, we use the `NoWitnesses` variant, which also keeps track
/// of potential unreachable sub-patterns (in the presence of or-patterns). When checking
/// exhaustiveness of a whole match, we use the `WithWitnesses` variant, which carries a list of
/// witnesses of non-exhaustiveness when there are any.
/// Which variant to use is dictated by `ArmType`.
#[derive(Debug)]
enum Usefulness<'p, 'tcx> {
    /// If we don't care about witnesses, simply remember if the pattern was useful.
    NoWitnesses { useful: bool },
    /// Carries a list of witnesses of non-exhaustiveness. If empty, indicates that the whole
    /// pattern is unreachable.
    WithWitnesses(Vec<Witness<'p, 'tcx>>),
}

impl<'p, 'tcx> Usefulness<'p, 'tcx> {
    fn new_useful(preference: ArmType) -> Self {
        match preference {
            // A single (empty) witness of reachability.
            ArmType::FakeExtraWildcard => Usefulness::WithWitnesses(vec![Witness(vec![])]),
            ArmType::RealArm => Usefulness::NoWitnesses { useful: true },
        }
    }

    fn new_not_useful(preference: ArmType) -> Self {
        match preference {
            ArmType::FakeExtraWildcard => Usefulness::WithWitnesses(vec![]),
            ArmType::RealArm => Usefulness::NoWitnesses { useful: false },
        }
    }

    fn is_useful(&self) -> bool {
        match self {
            Self::NoWitnesses { useful } => *useful,
            Self::WithWitnesses(witnesses) => !witnesses.is_empty(),
        }
    }

    /// Combine usefulnesses from two branches. This is an associative operation.
    fn extend(&mut self, other: Self) {
        match (&mut *self, other) {
            (Self::WithWitnesses(_), Self::WithWitnesses(o)) if o.is_empty() => {}
            (Self::WithWitnesses(s), Self::WithWitnesses(o)) if s.is_empty() => {
                *self = Usefulness::WithWitnesses(o)
            }
            (Self::WithWitnesses(s), Self::WithWitnesses(o)) => s.extend(o),
            (Self::NoWitnesses { useful: s_useful }, Self::NoWitnesses { useful: o_useful }) => {
                *s_useful = *s_useful || o_useful
            }
            _ => unreachable!(),
        }
    }

    /// After calculating usefulness after a specialization, call this to reconstruct a usefulness
    /// that makes sense for the matrix pre-specialization. This new usefulness can then be merged
    /// with the results of specializing with the other constructors.
    fn apply_constructor(
        self,
        pcx: PatContext<'_, 'p, 'tcx>,
        matrix: &Matrix<'p, 'tcx>, // used to compute missing ctors
        ctor: &Constructor,
    ) -> Self {
        match self {
            Self::NoWitnesses { .. } => self,
            Self::WithWitnesses(ref witnesses) if witnesses.is_empty() => self,
            Self::WithWitnesses(witnesses) => {
                let new_witnesses = if let Constructor::Missing { .. } = ctor {
                    // We got the special `Missing` constructor, so each of the missing constructors
                    // gives a new pattern that is not caught by the match. We list those patterns.
                    let new_patterns = if pcx.is_non_exhaustive {
                        // Here we don't want the user to try to list all variants, we want them to add
                        // a wildcard, so we only suggest that.
                        vec![DeconstructedPat::wildcard(pcx.ty)]
                    } else {
                        let mut split_wildcard = SplitWildcard::new(pcx);
                        split_wildcard.split(pcx, matrix.heads().map(DeconstructedPat::ctor));

                        // Construct for each missing constructor a "wild" version of this
                        // constructor, that matches everything that can be built with
                        // it. For example, if `ctor` is a `Constructor::Variant` for
                        // `Option::Some`, we get the pattern `Some(_)`.
                        split_wildcard
                            .iter_missing(pcx)
                            .map(|missing_ctor| {
                                DeconstructedPat::wild_from_ctor(pcx, missing_ctor.clone())
                            })
                            .collect()
                    };

                    witnesses
                        .into_iter()
                        .flat_map(|witness| {
                            new_patterns.iter().map(move |pat| {
                                Witness(
                                    witness
                                        .0
                                        .iter()
                                        .chain(once(pat))
                                        .map(DeconstructedPat::clone_and_forget_reachability)
                                        .collect(),
                                )
                            })
                        })
                        .collect()
                } else {
                    witnesses
                        .into_iter()
                        .map(|witness| witness.apply_constructor(pcx, ctor))
                        .collect()
                };
                Self::WithWitnesses(new_witnesses)
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum ArmType {
    FakeExtraWildcard,
    RealArm,
}

/// A witness of non-exhaustiveness for error reporting, represented
/// as a list of patterns (in reverse order of construction) with
/// wildcards inside to represent elements that can take any inhabitant
/// of the type as a value.
///
/// A witness against a list of patterns should have the same types
/// and length as the pattern matched against. Because Rust `match`
/// is always against a single pattern, at the end the witness will
/// have length 1, but in the middle of the algorithm, it can contain
/// multiple patterns.
///
/// For example, if we are constructing a witness for the match against
///
/// ```ignore
/// struct Pair(Option<(u32, u32)>, bool);
///
/// match (p: Pair) {
///    Pair(None, _) => {}
///    Pair(_, false) => {}
/// }
/// ```
///
/// We'll perform the following steps:
/// 1. Start with an empty witness
///     `Witness(vec![])`
/// 2. Push a witness `true` against the `false`
///     `Witness(vec![true])`
/// 3. Push a witness `Some(_)` against the `None`
///     `Witness(vec![true, Some(_)])`
/// 4. Apply the `Pair` constructor to the witnesses
///     `Witness(vec![Pair(Some(_), true)])`
///
/// The final `Pair(Some(_), true)` is then the resulting witness.
#[derive(Debug)]
pub struct Witness<'p, 'tcx>(Vec<DeconstructedPat<'p, 'tcx>>);

impl<'p, 'tcx> Witness<'p, 'tcx> {
    /// Asserts that the witness contains a single pattern, and returns it.
    fn single_pattern(self) -> DeconstructedPat<'p, 'tcx> {
        assert_eq!(self.0.len(), 1);
        self.0.into_iter().next().unwrap()
    }

    /// Constructs a partial witness for a pattern given a list of
    /// patterns expanded by the specialization step.
    ///
    /// When a pattern P is discovered to be useful, this function is used bottom-up
    /// to reconstruct a complete witness, e.g., a pattern P' that covers a subset
    /// of values, V, where each value in that set is not covered by any previously
    /// used patterns and is covered by the pattern P'. Examples:
    ///
    /// left_ty: tuple of 3 elements
    /// pats: [10, 20, _]           => (10, 20, _)
    ///
    /// left_ty: struct X { a: (bool, &'static str), b: usize}
    /// pats: [(false, "foo"), 42]  => X { a: (false, "foo"), b: 42 }
    fn apply_constructor(mut self, pcx: PatContext<'_, 'p, 'tcx>, ctor: &Constructor) -> Self {
        let pat = {
            let len = self.0.len();
            let arity = ctor.arity(pcx);
            let pats = self.0.drain((len - arity)..).rev();
            let fields = Fields::from_iter(pcx.cx, pats);
            DeconstructedPat::new(ctor.clone(), fields, pcx.ty)
        };

        self.0.push(pat);

        self
    }
}

/// Algorithm from <http://moscova.inria.fr/~maranget/papers/warn/index.html>.
/// The algorithm from the paper has been modified to correctly handle empty
/// types. The changes are:
///   (0) We don't exit early if the pattern matrix has zero rows. We just
///       continue to recurse over columns.
///   (1) all_constructors will only return constructors that are statically
///       possible. E.g., it will only return `Ok` for `Result<T, !>`.
///
/// This finds whether a (row) vector `v` of patterns is 'useful' in relation
/// to a set of such vectors `m` - this is defined as there being a set of
/// inputs that will match `v` but not any of the sets in `m`.
///
/// All the patterns at each column of the `matrix ++ v` matrix must have the same type.
///
/// This is used both for reachability checking (if a pattern isn't useful in
/// relation to preceding patterns, it is not reachable) and exhaustiveness
/// checking (if a wildcard pattern is useful in relation to a matrix, the
/// matrix isn't exhaustive).
///
/// `is_under_guard` is used to inform if the pattern has a guard. If it
/// has one it must not be inserted into the matrix. This shouldn't be
/// relied on for soundness.
fn is_useful<'p, 'tcx>(
    cx: &MatchCheckContext<'p, 'tcx>,
    matrix: &Matrix<'p, 'tcx>,
    v: &PatStack<'p, 'tcx>,
    witness_preference: ArmType,
    is_under_guard: bool,
    is_top_level: bool,
) -> Usefulness<'p, 'tcx> {
    let Matrix { patterns: rows, .. } = matrix;

    // The base case. We are pattern-matching on () and the return value is
    // based on whether our matrix has a row or not.
    // NOTE: This could potentially be optimized by checking rows.is_empty()
    // first and then, if v is non-empty, the return value is based on whether
    // the type of the tuple we're checking is inhabited or not.
    if v.is_empty() {
        let ret = if rows.is_empty() {
            Usefulness::new_useful(witness_preference)
        } else {
            Usefulness::new_not_useful(witness_preference)
        };
        return ret;
    }

    let ty = v.head().ty().bottom_ty();
    let pcx = PatContext {
        cx,
        ty,
        is_top_level,
        is_non_exhaustive: false,
    };

    // If the first pattern is an or-pattern, expand it.
    let mut ret = Usefulness::new_not_useful(witness_preference);
    if v.head().is_or_pat() {
        // expanding or-pattern
        // We try each or-pattern branch in turn.
        let mut matrix = matrix.clone();
        for v in v.expand_or_pat() {
            let usefulness = is_useful(cx, &matrix, &v, witness_preference, is_under_guard, false);
            ret.extend(usefulness);
            // If pattern has a guard don't add it to the matrix.
            if !is_under_guard {
                // We push the already-seen patterns into the matrix in order to detect redundant
                // branches like `Some(_) | Some(0)`.
                matrix.push(v);
            }
        }
    } else {
        let v_ctor = v.head().ctor();

        // We split the head constructor of `v`.
        let split_ctors = v_ctor.split(pcx, matrix.heads().map(DeconstructedPat::ctor));
        // For each constructor, we compute whether there's a value that starts with it that would
        // witness the usefulness of `v`.
        let start_matrix = &matrix;
        for ctor in split_ctors {
            // We cache the result of `Fields::wildcards` because it is used a lot.
            let spec_matrix = start_matrix.specialize_constructor(pcx, &ctor);
            let v = v.pop_head_constructor(cx, &ctor);
            let usefulness = is_useful(
                cx,
                &spec_matrix,
                &v,
                witness_preference,
                is_under_guard,
                false,
            );
            let usefulness = usefulness.apply_constructor(pcx, start_matrix, &ctor);
            ret.extend(usefulness);
        }
    }

    if ret.is_useful() {
        v.head().set_reachable();
    }

    ret
}

/// The entrypoint for the usefulness algorithm. Computes whether a match is exhaustive and which
/// of its arms are reachable.
///
/// Note: the input patterns must have been lowered through
/// `check_match::MatchVisitor::lower_pattern`.
fn compute_match_usefulness<'p, 'tcx>(
    cx: &MatchCheckContext<'p, 'tcx>,
    arms: &[MatchArm<'p, 'tcx>],
    src_ty: &'tcx Type<'tcx>,
) -> UsefulnessReport<'p, 'tcx> {
    let mut matrix = Matrix::empty();
    let arm_usefulness: Vec<_> = arms
        .iter()
        .copied()
        .map(|arm| {
            let v = PatStack::from_pattern(arm.pat);
            is_useful(cx, &matrix, &v, ArmType::RealArm, arm.has_guard, true);
            if !arm.has_guard {
                matrix.push(v);
            }
            let reachability = if arm.pat.is_reachable() {
                let pats = arm.pat.unreachable_sub_pats(cx);

                Reachability::Reachable {
                    unreachable_sub_patterns: pats,
                }
            } else {
                Reachability::Unreachable
            };
            (arm, reachability)
        })
        .collect();

    let wild_pattern = cx.pattern_arena.alloc(DeconstructedPat::wildcard(src_ty));
    let v = PatStack::from_pattern(wild_pattern);
    let usefulness = is_useful(cx, &matrix, &v, ArmType::FakeExtraWildcard, false, true);
    let non_exhaustiveness_witnesses = match usefulness {
        Usefulness::WithWitnesses(pats) => pats.into_iter().map(|w| w.single_pattern()).collect(),
        Usefulness::NoWitnesses { .. } => unreachable!(),
    };
    UsefulnessReport {
        arm_usefulness,
        non_exhaustiveness_witnesses,
    }
}

pub fn check_match<'tcx>(
    head_ty: &'tcx Type<'tcx>,
    arms: &[CaseArm<'_, 'tcx>],
    has_else: bool,
) -> Result<(), Vec<SemanticError<'tcx>>> {
    let pattern_arena = Arena::default();
    let tree_pattern_arena = Arena::default();
    let cx = MatchCheckContext {
        pattern_arena: &pattern_arena,
        tree_pattern_arena: &tree_pattern_arena,
    };

    let mut arms2: Vec<_> = arms
        .iter()
        .map(|arm| {
            let pattern: &_ = cx
                .pattern_arena
                .alloc(DeconstructedPat::from_pat(&cx, arm.pattern()));

            MatchArm {
                pat: pattern,
                has_guard: false,
            }
        })
        .collect();
    // else
    if has_else {
        let pattern: &_ = cx.pattern_arena.alloc(DeconstructedPat::wildcard(head_ty));
        arms2.push(MatchArm {
            pat: pattern,
            has_guard: false,
        })
    }

    let report = compute_match_usefulness(&cx, &arms2, head_ty);

    // Check if the match is exhaustive.
    let mut errors = vec![];

    // unreachable pattern
    for (i, (arm, reachability)) in report.arm_usefulness.iter().enumerate() {
        match reachability {
            Reachability::Reachable {
                unreachable_sub_patterns,
            } => {
                for sub_pat in unreachable_sub_patterns {
                    errors.push(SemanticError::UnreachablePattern {
                        pattern: sub_pat.to_string(),
                    });
                }
            }
            Reachability::Unreachable => {
                if has_else && i == (report.arm_usefulness.len() - 1) {
                    // "else"
                    errors.push(SemanticError::UnreachableElseClause);
                } else {
                    let pat = arm.pat.to_pat(&cx);

                    errors.push(SemanticError::UnreachablePattern {
                        pattern: pat.kind().to_string(),
                    });
                }
            }
        }

        if matches!(reachability, Reachability::Unreachable) {
            if has_else && i == (report.arm_usefulness.len() - 1) {
                // "else"
                errors.push(SemanticError::UnreachableElseClause);
            } else {
                let pat = arm.pat.to_pat(&cx);

                errors.push(SemanticError::UnreachablePattern {
                    pattern: pat.to_string(),
                });
            }
        }
    }
    // non exhaustiveness
    for pat in report.non_exhaustiveness_witnesses {
        let pat = pat.to_pat(&cx);

        errors.push(SemanticError::NonExhaustivePattern {
            pattern: pat.kind().to_string(),
        })
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Recursively expand this pattern into its subpatterns. Only useful for or-patterns.
fn expand_or_pat<'p, 'tcx>(pat: &'p Pattern<'p, 'tcx>) -> Vec<&'p Pattern<'p, 'tcx>> {
    fn expand<'p, 'tcx>(pat: &'p Pattern<'p, 'tcx>, vec: &mut Vec<&'p Pattern<'p, 'tcx>>) {
        if let PatternKind::Or(pats) = pat.kind() {
            for pat in pats {
                expand(pat, vec);
            }
        } else {
            vec.push(pat)
        }
    }

    let mut pats = Vec::new();
    expand(pat, &mut pats);
    pats
}

#[cfg(test)]
mod tests_int_range {
    use super::*;

    #[test]
    fn is_integral() {
        assert!(IntRange::is_integral(&Type::Int64));
    }

    #[test]
    fn signed_bias() {
        let bias = IntRange::signed_bias(&Type::Int64);
        assert_eq!(bias, 9223372036854775808i128);
    }

    #[test]
    fn i64_min() {
        let r = IntRange::from_i64(i64::MIN);
        let (low, high) = r.boundaries();

        assert!(r.is_singleton());
        assert_eq!(low, 0);
        assert_eq!(high, 0);

        let pat = r.to_pat(&Type::Int64);
        let kind = pat.kind();

        if let PatternKind::Integer(n) = kind {
            assert_eq!(*n, i64::MIN);
        } else {
            unreachable!("pattern must be integer")
        }
    }

    #[test]
    fn i64_max() {
        let r = IntRange::from_i64(i64::MAX);
        let (low, high) = r.boundaries();

        assert!(r.is_singleton());
        assert_eq!(low, 18446744073709551615u128);
        assert_eq!(high, 18446744073709551615u128);

        let pat = r.to_pat(&Type::Int64);
        let kind = pat.kind();

        if let PatternKind::Integer(n) = kind {
            assert_eq!(*n, i64::MAX);
        } else {
            unreachable!("pattern must be integer")
        }
    }

    #[test]
    fn from_range() {
        let r = IntRange::from_range(i64::MIN, i64::MAX, &Type::Int64, RangeEnd::Included);
        let (low, high) = r.boundaries();

        assert!(!r.is_singleton());
        assert_eq!(low, 0);
        assert_eq!(high, 18446744073709551615u128);
    }
}

#[cfg(test)]
mod tests_deconstructed_pat {
    use super::*;

    #[test]
    fn from_pat() {
        let pattern_arena = Arena::default();
        let tree_pattern_arena = Arena::default();
        let cx = MatchCheckContext {
            pattern_arena: &pattern_arena,
            tree_pattern_arena: &tree_pattern_arena,
        };
        let kind = PatternKind::Range {
            lo: 1,
            hi: 2,
            end: RangeEnd::Included,
        };
        let pat = Pattern::new(kind);
        pat.assign_ty(&Type::Int64);
        let dc_pat = DeconstructedPat::from_pat(&cx, &pat);

        assert_eq!(dc_pat.ty(), &Type::Int64);
    }
}
