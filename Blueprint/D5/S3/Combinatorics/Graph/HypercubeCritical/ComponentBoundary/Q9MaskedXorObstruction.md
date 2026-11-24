# Geometric restrictions on the two parities

## Abstract

XOR intersections of saturated nine-cube components

**Theorem 1.1 (Disjoint and one-parity intersections).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedXorObstruction.overlapping_mask_xor_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedXorObstruction.overlapping_mask_xor_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let two four-axis masks share exactly three axes, with exclusive axes a and b. Take their respective connected components on a common balanced support. Assume that each component has a singular Huang parity defect for its own mask. The two singular defects may use different parities. The XOR intersection consists of the vertices of the first component whose images under the two exclusive flips belong to the second component.

Each singular defect gives an ambient eigenvector at eigenvalue 2. The absolute-value eigenfunction is strictly positive along every path in the component. Multiplying it by the common switching function gives the signed eigenvector on that component. The ambient squared-norm identity forces its masked image to vanish outside the component.

The common cell uses the bits pinned by the second component on a and by the first component on b. Any edge in a common direction between the two components has both endpoints in their ordinary intersection. Such edges are absent when the intersection is empty or confined to one parity, so the cross term in the signed transfer vanishes.

When the components are disjoint both signed XOR sums vanish. A singleton XOR intersection on either parity would give a single nonzero summand. When the ordinary intersection is nonempty and confined to one parity, its common-cell dot product is positive by the shared switching. The two signed XOR sums are three and four times this positive dot product, forcing the XOR intersection to meet both parities.

This restricts the configurations of saturated four-axis components for Hong, Wu and Xia’s Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedXorObstruction.overlapping_mask_xor_intersection`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedXorTransfer](Q9SignedXorTransfer.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseFace](Q9SparseFace.md)
