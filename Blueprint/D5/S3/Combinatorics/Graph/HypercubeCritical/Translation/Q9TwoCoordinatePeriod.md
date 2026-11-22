# Two-coordinate periods in Q9

## Abstract

A 258-point subcubic induced subgraph of Q9 has no two-coordinate translation period.

**Theorem 1.1 (Two distinct flips cannot preserve a 258-point subcubic support).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TwoCoordinatePeriod.not_two_coordinate_period`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TwoCoordinatePeriod.not_two_coordinate_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be a set of 258 vertices in the Boolean 9-cube whose induced graph has maximum degree at most 3. For any distinct coordinates i and j, some vertex of U leaves U when both coordinates are flipped.

For nonnegative coordinate weights w, let H be the weighted signed Huang operator. On the 258-point support U, extending by zero, applying H and restricting to the complement defines a linear map from dimension 258 to dimension 254. A nonzero kernel vector extends to a nonzero f with both f and Hf supported on U. If each selected vertex has total incident weight at most d, the unit absolute values of the edge signs bound Hf by d times the maximum absolute entry of f. Applying the bound to Hf at a maximizing vertex of f and using the weighted Huang square gives the inequality Σ w² ≤ d² from Daniel V. Mathews, The sensitivity conjecture, induced subgraphs of cubes, and Clifford algebras, Theorem 1.2. https://doi.org/10.4171/jems/1180

Suppose flipping i and j preserves U. The two single-flip neighbors of any vertex are exchanged by the double flip, because the flips commute and each is an involution. Applying the period at each neighbor in U shows that the two directions occur together. Weights 0 at i, 2 at j and 1 elsewhere therefore give a weighted degree equal to the induced degree at each vertex of U. The squared weights sum to 11, contradicting the bound of 9.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TwoCoordinatePeriod.not_two_coordinate_period`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](../ComponentBoundary/Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells](../ComponentBoundary/Q9SignedContactCells.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension](../SupportedEigenDimension.md)
