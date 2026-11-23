# A bound from a singular component defect

## Abstract

Weighted direction bounds in components of the nine-cube

**Theorem 1.1 (A singular component defect forces a large weighted row).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedProfile.exists_weighted_row_of_componentDefect_det_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedProfile.exists_weighted_row_of_componentDefect_det_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an actual component of an induced subgraph of the nine-cube and one retained parity. If the weighted Huang defect is singular, some vertex of the component has incident direction weight at least the Euclidean norm of the nonnegative weight vector.

The determinant identity uses the signed block between the two parities of the component. A nonzero kernel vector of the defect is an eigenvector of the block times its transpose with eigenvalue equal to the sum of squares of the weights. The infinity operator norms of the block and its transpose are bounded by the maximum weighted row of the component. Their product bounds the eigenvalue, which gives the claimed square-root inequality.

For a 258-vertex subcubic candidate, exists_two_weighted_singular_components gives two distinct actual components for each retained parity, chosen before the weights. Each of those same two components therefore satisfies this bound for every nonnegative weight vector. The maximizing vertex may depend on the weights.

If one of these universally singular components is cubic, let F be the family of its actual direction triples. For every nonnegative w, the maximum over D in F of the sum of w on D is at least the Euclidean norm of w. A rational w excludes a proposed family if it is nonnegative and the squared sum on every triple is strictly below the sum of squares of w.

As a geometric consequence for such a cubic component, let a be a unit vector whose coordinates sum to zero and set m equal to minus its smallest coordinate. The weight w = a + m is nonnegative, its squared norm is 1 + 9m², and every triple weight increases by 3m. The maximum triple dot product with a is therefore at least sqrt(1 + 9m²) − 3m. The eight coordinates other than a minimizing coordinate sum to m, so Cauchy–Schwarz gives 1 ≥ m² + m²/8 and m ≤ sqrt(8)/3. Rationalizing the bound gives 1/(sqrt(1 + 9m²) + 3m) ≥ 1/(3 + sqrt(8)) = 3 − sqrt(8). The supporting-halfspace description of the convex hull of the triple incidence vectors then gives a ball of this radius centered at (1/3, …, 1/3) in the hyperplane of coordinate sum three. This geometric derivation is given here in prose.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedProfile.exists_weighted_row_of_componentDefect_det_eq_zero`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation](Q9ComponentSaturation.md)
