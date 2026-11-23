# One masked component for all supported weights

## Abstract

Universal sparse-weight singularity on a nine-cube face

**Theorem 1.1 (Sparse-weight singularity passes to a fixed actual component).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseFace.exists_fixed_singular_masked_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseFace.exists_fixed_singular_masked_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a parity and an actual component of an induced subgraph of the nine-cube. Suppose its weighted Huang defect is singular for every real coordinate weighting supported on the mask I. A single connected component of the graph retaining the axes in I has singular defect on the same parity for all those weightings.

Each vertex of the chosen component retains exactly the original incident directions in I. The coordinates outside I are constant throughout the component. Both parity sides are the intersections of the original parity sides with this same component's support.

Put a polynomial variable on each retained axis and zero elsewhere. Evaluation at real weights commutes with the determinant, so the determinant is identically zero by polynomial extensionality over the reals. The masked components separate the signed Gram matrix into blocks. The polynomial ring is an integral domain, so one block has identically zero determinant and can be selected before specialization.

For a four-axis mask, the chosen component lies in one four-dimensional face. A census of such supports can therefore impose conditions on its two parity projections jointly. The census is a separate input to this application of the theorem toward Hong, Wu and Xia's Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseFace.exists_fixed_singular_masked_component`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation](Q9ComponentSaturation.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum](Q9MaskedSpectrum.md)
