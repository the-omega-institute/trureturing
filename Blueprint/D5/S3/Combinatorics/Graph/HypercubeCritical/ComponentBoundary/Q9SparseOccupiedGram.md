# Sparse occupied Gram obstruction

## Abstract

Sparse occupied Gram obstruction

**Theorem 1.1 (Disjoint column supports force a trivial complementary kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.eq_zero_of_sparse_occupied_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.eq_zero_of_sparse_occupied_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram matrices of two row sets sum to a scalar identity. If distinct columns never share a nonzero row in the first matrix, its Gram matrix is diagonal. Each diagonal entry strictly below the common scalar gives a positive diagonal entry in the complementary Gram, forcing its kernel to vanish.

**Definition 1.2 (Masked transverse contact).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.maskContact`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.maskContact` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An occupied projected row meets a paired column by one coordinate flip in the chosen transverse mask.

**Theorem 1.3 (Sparse contact counts exclude a boundary kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.eq_zero_of_sparse_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.eq_zero_of_sparse_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The switching signs turn occupied mask contacts into unit entries. At most one contact per row and fewer contacts per column than the mask size establish strict positivity of the complementary Gram.

**Theorem 1.4 (Obstruction to universal weighted sharpness).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.not_universal_boundary_of_sparse_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.not_universal_boundary_of_sparse_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dominant-axis saturation would provide a nonzero empty-fibre kernel for every mask. A sparse contact mask contradicts that requirement. This is the local test for the thirty-two regular order-ninety fold candidates in Hong–Wu–Xia Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.eq_zero_of_sparse_mask`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.eq_zero_of_sparse_occupied_gram`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.maskContact`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram.not_universal_boundary_of_sparse_mask`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel](Q9PositivePairedKernel.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary](../CoordinateHalves/Q9DominantAxisBoundary.md)
