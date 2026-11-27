# Concentrating Circuit Weights within Each Block

## Abstract

Integral changes of coordinates on the fibers of a partition.

**Theorem 1.1 (One weighted direction in each fiber).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.exists_weight_basis_by_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.exists_weight_basis_by_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A partition of the indices gives a product of the corresponding integral coordinate modules. Choose an integral basis in each fiber so its weight vector is the fiber gcd times a single basis vector. The combined basis respects the original fibers in both directions of the change of coordinates. The weight is zero on every other basis coordinate.

**Theorem 1.2 (Vanishing of a face coefficient under a supported change of basis).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.tuple_vanishing_iff_of_supported_change`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.tuple_vanishing_iff_of_supported_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both directions of a change of coordinates preserve a given subset, the old and new basis vectors on that subset span the same integral submodule. An alternating form of the corresponding degree vanishes on the old basis tuple exactly when it vanishes on the new one.

**Theorem 1.3 (Separating the zero-weight intersections of two faces).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.exists_basis_separating_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.exists_basis_separating_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition the indices by membership in the two faces. Each block has at most one weighted direction after an integral change of basis. If the first face has two indices outside the second, one of them has zero weight, so the two intersections with the zero-weight set differ. The changed coordinates preserve the spans of both faces.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.exists_basis_separating_faces`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.exists_weight_basis_by_fiber`
- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitWeightBlocks.tuple_vanishing_iff_of_supported_change`
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitWeightBasis](PuncturedCircuitWeightBasis.md)
