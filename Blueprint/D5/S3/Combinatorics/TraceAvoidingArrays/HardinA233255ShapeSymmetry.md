# Relabelling complementary pairs after both distinguished colours appear

## Abstract

Canonical proper boundaries preserve every completed-scanner continuation height.

When colours one and two have both appeared, every pair-label cell has two individual-colour lifts. A seven-cell row therefore has multiplicity 128. Permuting all three pair labels preserves each horizontal and antidiagonal inequality, so the entire continuation transfer respects that permutation at every height.

**Definition 1.1 (Proper six-cell boundaries).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.proper`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.proper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Adjacent labels differ.

**Definition 1.2 (Canonical boundary representatives).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.Shape`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.Shape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A proper six-cell word whose first two labels are zero and one.

**Definition 1.3 (Canonical relabelling).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.canonical`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.canonical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first label becomes zero, the second becomes one, and the remaining label becomes two. Properness makes the first two labels distinct.

**Theorem 1.4 (All-height canonical correspondence).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.completed_canonical_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.completed_canonical_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on continuation height reindexes actual compatible pair rows by the same label permutation. The completed-scanner continuation count therefore depends only on the canonical boundary. The initial and unfinished scanner sectors still require their own weighted aggregation.

**Definition 1.5 (Sixteen actual canonical boundaries).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.representatives`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit list contains every proper six-cell boundary beginning zero, one, exactly once.

**Definition 1.6 (Boundary label normalization).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.normalize`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.normalize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any six-cell boundary p, a label equal to p(0) becomes zero; otherwise a label equal to p(1) becomes one; every remaining label becomes two. The first test takes precedence even when the first two labels coincide. Proper boundaries have distinct first two labels.

**Definition 1.7 (Complete boundary enumeration).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.shapeEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.shapeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A proved equivalence identifies the sixteen indices with the actual canonical-boundary subtype, including representatives missing the third label.

**Definition 1.8 (Successor class).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.classOf`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.classOf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any six-cell boundary, normalize its labels, then test representatives zero through fourteen in order, returning the first matching index or fifteen if none matches. For a proper boundary, the normalized word has a unique matching representative among all sixteen, and this lookup returns its index. For a nonproper boundary, the fallback need not identify a matching representative.

**Definition 1.9 (Actual compatible-row matrix).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.K`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Entry i,j counts proper seven-cell pair rows compatible with representative i whose six-cell suffix has canonical class j.

**Definition 1.10 (Completed-scanner vector).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.F`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At height m this is 128 to the power m times K to the power m applied to the all-ones vector.

**Theorem 1.11 (Exact completed-state matrix powers).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.completed_transfer_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.completed_transfer_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural continuation height and every proper labelled six-cell boundary, the original completed-scanner continuation equals F at its canonical class. The induction groups actual compatible pair rows by their successor class. It does not presume a scalar count identity or fit a recurrence. The unfinished scanner sector and anchored initial multiplicities are handled below.

**Theorem 1.12 (Original literal count at every positive height).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.literal_canonical_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.literal_canonical_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, the individual-array count at height m plus one equals 16 times 128 to the power m plus 32 times the sum of F at m over all sixteen actual canonical boundaries. The unfinished scanner has seen colour one but not colour two. Its boundary is one of the two alternating words on labels zero and one. There is exactly one compatible proper row avoiding label two, with 128 lifts and the same suffix. Every row containing label two has 64 lifts and completes the scanner; all seven cells, including the discarded first cell, participate in this test. Induction gives twice the unfinished continuation equal to the completed continuation plus 128 to the power m. The anchored first-row fibres contribute 32 unfinished lifts at the alternating shape, 16 completed lifts there, and 32 completed lifts at each other shape. These disjoint literal fibres yield the formula without an orbit quotient. HardinA233255Recurrence proves the recurrence using an exact finite vector certificate and unbounded polynomial propagation.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.F`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.K`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.Shape`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.canonical`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.classOf`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.completed_canonical_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.completed_transfer_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.literal_canonical_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.normalize`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.representatives`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.shapeEquiv`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
