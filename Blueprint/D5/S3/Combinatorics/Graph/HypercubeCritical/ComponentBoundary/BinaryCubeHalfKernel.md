# Binary adjacency on cube halves

## Abstract

Binary adjacency on cube halves

**Definition 1.1 (Binary cube adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the translated word over all single-coordinate involutions.

**Theorem 1.2 (Square of binary cube adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_square`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each diagonal term is an involution and each pair of distinct coordinate flips cancels in characteristic two. Thus the square is multiplication by the dimension.

**Theorem 1.3 (Odd-dimensional adjacency is an involution).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An odd number of diagonal terms remains after the cancellation.

**Theorem 1.4 (An even-dimensional kernel word is determined by one half).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_eq_zero_iff_half`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_eq_zero_iff_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two half-cube equations reduce to one because odd-dimensional adjacency is an involution.

**Theorem 1.5 (Reconstructing a kernel completion).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_add_eq_zero_iff_affine_half`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_add_eq_zero_iff_affine_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine formula determines the second half of the unknown word after adding the prescribed word. For Hong–Wu–Xia, arXiv:2610.09483 §7, Problem 2, the prescribed word can be the occupied singleton contacts of an axial fold.

**Theorem 1.6 (The four section equations for two deleted coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_two_sections_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_two_sections_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate flips along the first two axes move between adjacent sections. The remaining flips act within each section, so each section equation relates these three contributions.

**Theorem 1.7 (Opposite sections give a lower-dimensional kernel word).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_opposite_sections_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_opposite_sections_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two section equations have the same adjacent sections. Adding them in characteristic two cancels those terms. When the sum is nonzero, its support is bounded below by the minimum kernel weight in the smaller cube.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_add_eq_zero_iff_affine_half`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_eq_zero_iff_half`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_involutive`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_opposite_sections_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_square`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel.adjacency_two_sections_eq`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
