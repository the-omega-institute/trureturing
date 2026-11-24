# Weight transport and separation of centered outward images

## Abstract

Weight transport and separation of centered outward images

**Theorem 1.1 (Coordinate weights act by the center monomial).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.outward_monomial_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.outward_monomial_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a vertex the center monomial is the product of weights on the coordinates separating it from the center. An outward flip adds one such factor. Multiplication by the monomial intertwines the unit-weight and weighted outward differentials. When each weight is nonzero, the diagonal inverse gives a linear equivalence of the two kernels restricted to the same column support.

**Theorem 1.2 (Closed residuals at positive weighted distance cannot cancel).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.closed_pair_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.closed_pair_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two opposite closed residuals would lie in the intersection of both outward kernels. The exact difference-energy identity forces their common vector to vanish if the weighted squared center distance is positive.

**Theorem 1.3 (Single-center injectivity extends to the weighted two-center sum).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.weighted_pair_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.weighted_pair_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every outward image is closed under its own differential. Distinct centers and nonzero coordinate weights force two canceling images to vanish separately. The monomial diagonal equivalence transports unit-weight injectivity on each original column support into the weighted setting.

This algebraic implication prepares the actual paired-fibre boundary analysis for Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.closed_pair_eq_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.outward_monomial_mul`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge.weighted_pair_eq_zero`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference](CenterOutwardDifference.md)
