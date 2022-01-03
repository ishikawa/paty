//! Based on usefulness algorithm in Rust:
//! - https://github.com/rust-lang/rust/blob/d331cb710f0/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs
//! - https://github.com/rust-lang/rust/blob/d331cb710f0/compiler/rustc_mir_build/src/thir/pattern/deconstruct_pat.rs
use crate::{
    syntax::{Pattern, PatternKind, RangeEnd},
    typing::Type,
};
use std::{
    cell::Cell,
    cmp::{max, min},
    fmt,
    ops::RangeInclusive,
};

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
    bias: u128,
}

#[allow(dead_code)]
impl IntRange {
    #[inline]
    fn is_integral(ty: &Type) -> bool {
        matches!(ty, Type::Int64)
    }

    fn is_singleton(&self) -> bool {
        self.range.start() == self.range.end()
    }

    fn boundaries(&self) -> (u128, u128) {
        (*self.range.start(), *self.range.end())
    }

    // The return value of `signed_bias` should be XORed with an endpoint to encode/decode it.
    fn signed_bias(ty: &Type) -> u128 {
        match ty {
            Type::Int64 => 1u128 << (i64::BITS as u128 - 1),
        }
    }

    #[inline]
    fn from_const(value: i64) -> IntRange {
        let bias = Self::signed_bias(&Type::Int64);
        let val = u128::try_from(value + i64::try_from(bias).unwrap()).unwrap();

        IntRange {
            range: val..=val,
            bias,
        }
    }

    #[inline]
    fn from_range(lo: u128, hi: u128, ty: &Type, end: &RangeEnd) -> IntRange {
        // Perform a shift if the underlying types are signed,
        // which makes the interval arithmetic simpler.
        let bias = IntRange::signed_bias(ty);
        let (lo, hi) = (lo ^ bias, hi ^ bias);
        let offset = (*end == RangeEnd::Excluded) as u128;
        if lo > hi || (lo == hi && *end == RangeEnd::Excluded) {
            // This should have been caught earlier by E0030.
            unreachable!("malformed range pattern: {}..={}", lo, (hi - offset));
        }
        IntRange {
            range: lo..=(hi - offset),
            bias,
        }
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

    fn suspicious_intersection(&self, other: &Self) -> bool {
        // `false` in the following cases:
        // 1     ----      // 1  ----------   // 1 ----        // 1       ----
        // 2  ----------   // 2     ----      // 2       ----  // 2 ----
        //
        // The following are currently `false`, but could be `true` in the future (#64007):
        // 1 ---------       // 1     ---------
        // 2     ----------  // 2 ----------
        //
        // `true` in the following cases:
        // 1 -------          // 1       -------
        // 2       --------   // 2 -------
        let (lo, hi) = self.boundaries();
        let (other_lo, other_hi) = other.boundaries();
        (lo == other_hi || hi == other_lo) && !self.is_singleton() && !other.is_singleton()
    }

    /// Only used for displaying the range properly.
    fn to_pat(&self) -> Pattern {
        let (lo, hi) = self.boundaries();

        let bias = i64::try_from(self.bias).unwrap();
        let lo = i64::try_from(lo).unwrap() - bias;
        let hi = i64::try_from(hi).unwrap() - bias;

        let kind = if lo == hi {
            PatternKind::Integer(lo)
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
        let bias = self.bias;
        let (lo, hi) = (lo ^ bias, hi ^ bias);
        write!(f, "{}", lo)?;
        write!(f, "{}", RangeEnd::Included)?;
        write!(f, "{}", hi)
    }
}

/// A row of a matrix. Rows of len 1 are very common, which is why `SmallVec[_; 2]`
/// works well.
#[derive(Clone)]
struct PatStack<'p> {
    pats: Vec<&'p DeconstructedPat<'p>>,
}

#[allow(dead_code)]
impl<'p> PatStack<'p> {
    fn from_pattern(pat: &'p DeconstructedPat<'p>) -> Self {
        Self::from_vec(vec![pat])
    }

    fn from_vec(vec: Vec<&'p DeconstructedPat<'p>>) -> Self {
        PatStack { pats: vec }
    }

    fn is_empty(&self) -> bool {
        self.pats.is_empty()
    }

    fn len(&self) -> usize {
        self.pats.len()
    }

    fn head(&self) -> &'p DeconstructedPat<'p> {
        self.pats[0]
    }

    fn iter(&self) -> impl Iterator<Item = &DeconstructedPat<'p>> {
        self.pats.iter().copied()
    }

    // Recursively expand the first pattern into its subpatterns. Only useful if the pattern is an
    // or-pattern. Panics if `self` is empty.
    fn expand_or_pat<'a>(&'a self) -> impl Iterator<Item = PatStack<'p>> + 'a {
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
    fn pop_head_constructor(&self, ctor: &Constructor) -> PatStack<'p> {
        // We pop the head pattern and push the new fields extracted from the arguments of
        // `self.head()`.
        let mut new_fields = self.head().specialize(ctor);
        new_fields.extend_from_slice(&self.pats[1..]);
        PatStack::from_vec(new_fields)
    }
}

/// A 2D matrix.
#[derive(Clone)]
pub(super) struct Matrix<'p> {
    patterns: Vec<PatStack<'p>>,
}

#[allow(dead_code)]
impl<'p> Matrix<'p> {
    fn empty() -> Self {
        Matrix { patterns: vec![] }
    }

    /// Number of columns of this matrix. `None` is the matrix is empty.
    pub(super) fn column_count(&self) -> Option<usize> {
        self.patterns.get(0).map(|r| r.len())
    }

    /// Pushes a new row to the matrix. If the row starts with an or-pattern, this recursively
    /// expands it.
    fn push(&mut self, row: PatStack<'p>) {
        if !row.is_empty() && row.head().is_or_pat() {
            self.patterns.extend(row.expand_or_pat());
        } else {
            self.patterns.push(row);
        }
    }

    /// Iterate over the first component of each row
    fn heads<'a>(&'a self) -> impl Iterator<Item = &'p DeconstructedPat<'p>> + Clone + 'a {
        self.patterns.iter().map(|r| r.head())
    }

    /// This computes `S(constructor, self)`. See top of the file for explanations.
    fn specialize_constructor(&self, ctor: &Constructor) -> Matrix<'p> {
        let mut matrix = Matrix::empty();
        for row in &self.patterns {
            if ctor.is_covered_by(row.head().ctor()) {
                let new_row = row.pop_head_constructor(ctor);
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
impl<'p> fmt::Debug for Matrix<'p> {
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
impl<'p> fmt::Debug for PatStack<'p> {
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
#[allow(dead_code)]
pub enum Constructor {
    /// Wildcard pattern.
    Wildcard,
    /// Ranges of integer literal values (`2`, `2..=5` or `2..5`).
    IntRange(IntRange),
}

impl Constructor {
    /// Returns whether `self` is covered by `other`, i.e. whether `self` is a subset of `other`.
    /// For the simple cases, this is simply checking for equality. For the "grouped" constructors,
    /// this checks for inclusion.
    // We inline because this has a single call site in `Matrix::specialize_constructor`.
    pub(super) fn is_covered_by(&self, other: &Self) -> bool {
        // This must be kept in sync with `is_covered_by_any`.
        match (self, other) {
            // Wildcards cover anything
            (_, Constructor::Wildcard) => true,
            (Constructor::IntRange(self_range), Constructor::IntRange(other_range)) => {
                self_range.is_covered_by(other_range)
            }
            _ => unreachable!(
                "trying to compare incompatible constructors {:?} and {:?}",
                self, other
            ),
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
pub struct Fields<'p> {
    fields: &'p [DeconstructedPat<'p>],
}

impl<'p> Fields<'p> {
    fn empty() -> Self {
        Fields { fields: &[] }
    }

    /// Creates a new list of wildcard fields for a given constructor. The result must have a
    /// length of `constructor.arity()`.
    pub(super) fn wildcards(_ty: Type, constructor: &Constructor) -> Self {
        match constructor {
            Constructor::IntRange(..) | Constructor::Wildcard => Fields::empty(),
        }
    }

    /// Returns the list of patterns.
    pub fn iter_patterns<'a>(&'a self) -> impl Iterator<Item = &'p DeconstructedPat<'p>> {
        self.fields.iter()
    }
}

/// Values and patterns can be represented as a constructor applied to some fields. This represents
/// a pattern in this form.
/// This also keeps track of whether the pattern has been found reachable during analysis. For this
/// reason we should be careful not to clone patterns for which we care about that. Use
/// `clone_and_forget_reachability` if you're sure.
#[derive(Debug)]
#[allow(dead_code)]
pub struct DeconstructedPat<'p> {
    ctor: Constructor,
    fields: Fields<'p>,
    ty: Type,
    reachable: Cell<bool>,
}

#[allow(dead_code)]
impl<'p> DeconstructedPat<'p> {
    pub(super) fn wildcard(ty: Type) -> Self {
        Self::new(Constructor::Wildcard, Fields::empty(), ty)
    }

    pub(super) fn new(ctor: Constructor, fields: Fields<'p>, ty: Type) -> Self {
        DeconstructedPat {
            ctor,
            fields,
            ty,
            reachable: Cell::new(false),
        }
    }

    pub fn from_pat(pat: &Pattern) -> Self {
        let ctor;
        let fields;
        match pat.kind() {
            PatternKind::Wildcard => {
                ctor = Constructor::Wildcard;
                fields = Fields::empty();
            }
            PatternKind::Integer(value) => {
                let int_range = IntRange::from_const(*value);

                ctor = Constructor::IntRange(int_range);
                fields = Fields::empty();
            }
            &PatternKind::Range { lo, hi, end } => {
                let bias = i64::MIN.abs() as i128;
                let lo_biased = u128::try_from((lo as i128) + bias).unwrap();
                let hi_biased = u128::try_from((hi as i128) + bias).unwrap();
                let int_range = IntRange::from_range(lo_biased, hi_biased, &Type::Int64, &end);

                ctor = Constructor::IntRange(int_range);
                fields = Fields::empty();
            }
        }

        DeconstructedPat::new(ctor, fields, Type::Int64)
    }
    pub(super) fn ctor(&self) -> &Constructor {
        &self.ctor
    }

    pub fn iter_fields<'a>(&'a self) -> impl Iterator<Item = &'p DeconstructedPat<'p>> {
        self.fields.iter_patterns()
    }

    pub(super) fn is_or_pat(&self) -> bool {
        false
    }

    /// Specialize this pattern with a constructor.
    /// `other_ctor` can be different from `self.ctor`, but must be covered by it.
    pub fn specialize<'a>(&'a self, other_ctor: &Constructor) -> Vec<&'p DeconstructedPat<'p>> {
        match (&self.ctor, other_ctor) {
            (Constructor::Wildcard, _) => {
                // We return a wildcard for each field of `other_ctor`.
                Fields::wildcards(self.ty.clone(), other_ctor)
                    .iter_patterns()
                    .collect()
            }
            _ => self.fields.iter_patterns().collect(),
        }
    }
}

/// The arm of a match expression.
#[derive(Clone, Copy)]
pub struct MatchArm<'p> {
    /// The pattern must have been lowered through `check_match::MatchVisitor::lower_pattern`.
    pub pat: &'p DeconstructedPat<'p>,
    pub has_guard: bool,
}

/// Indicates whether or not a given arm is reachable.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum Reachability {
    /// The arm is reachable.
    Reachable,
    /// The arm is unreachable.
    Unreachable,
}

/// The output of checking a match for exhaustiveness and arm reachability.
#[allow(dead_code)]
pub struct UsefulnessReport<'p> {
    /// For each arm of the input, whether that arm is reachable after the arms above it.
    pub arm_usefulness: Vec<(MatchArm<'p>, Reachability)>,
    /// If the match is exhaustive, this is empty. If not, this contains witnesses for the lack of
    /// exhaustiveness.
    pub non_exhaustiveness_witnesses: Vec<DeconstructedPat<'p>>,
}

#[allow(dead_code)]
/// The entrypoint for the usefulness algorithm. Computes whether a match is exhaustive and which
/// of its arms are reachable.
///
/// Note: the input patterns must have been lowered through
/// `check_match::MatchVisitor::lower_pattern`.
pub fn compute_match_usefulness<'p>(arms: &[MatchArm<'p>]) -> UsefulnessReport<'p> {
    todo!()
}
