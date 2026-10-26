# Exact partition by actual residual cores

## Abstract

Exact partition by actual residual cores.

Fiber a b m n K is literally the actual residual/JointReduction/per-side-preserving subtype used in core_positive_vectors_inject. It retains every normalized integer function at the original dimensions. The core index records its two exact dimensions and its full normalized function; no quotient or representative replaces any original array.

**Definition 1.1 (The unchanged actual fixed-core fiber).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.Fiber`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.Fiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership is precisely Residual a b g, JointReduction g to the complete K function, and equivalence of all-minima containment separately on each physical side of the original and reduced rectangles.

**Theorem 1.2 (Distinct cores cannot share an actual array).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residual_core_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residual_core_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a,b,m,n and every actual unit-edge integer height function h, if h reduces by arbitrary legal joint sequences to K and L in the existing Core a b family, then K=L. The existing joint_reduced_core_unique theorem gives equality of both dimensions and full functions. Injectivity of the finite dependent Core representation transports precisely that equality to the original Core indices.

**Definition 1.3 (An equivalence retaining every original array).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residualCoreEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residualCoreEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive a,b, total at least five, and both dimensions at least 2(a+b)-1, residualCoreEquiv sends each original residual array to its unique exact Core fiber. Its inverse forgets only the core index and retains the identical full function. Existence uses residual_core_exists, including its derived positive run counts; injectivity uses residual_core_unique. Consequently every original array is present exactly once.

**Theorem 1.4 (The original count is the sum of actual fiber cardinalities).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residual_count_eq_sum_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residual_count_eq_sum_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural a,b with a+b at least five and every m,n at least 2(a+b)-1, the unchanged residualCount a b m n equals the sum, over every K in the same finite Core a b, of Nat.card (Fiber a b m n K). The original count is converted to the cardinality of its actual residual subtype by the existing finite-set identity. The actual equivalence supplies cardinality equality, and pinned mathlib Nat.card_sigma computes the finite sum. Fiber finiteness follows by injection into the proved finite residual class.

This equality counts actual fibers. Identification of those fibers with positive length vectors and the final polynomial identity are separate conclusions and are not hypotheses of this partition theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.Fiber`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residualCoreEquiv`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residual_core_unique`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPartitionCount.residual_count_eq_sum_fibers`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraPartitionCore](MiuraPartitionCore.md)
