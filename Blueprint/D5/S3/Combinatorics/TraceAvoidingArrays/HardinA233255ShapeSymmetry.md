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

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.Shape`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.canonical`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.completed_canonical_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.proper`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
