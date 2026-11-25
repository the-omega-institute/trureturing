# Exterior residual demands of a balanced cube support

## Abstract

Exterior residual demands of a balanced cube support

**Theorem 1.1 (Exterior cancellation bounds the completion size).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ExteriorResidualBudget.weighted_exterior_residual_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ExteriorResidualBudget.weighted_exterior_residual_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Huang action on the full cube extends the switching vector of an induced balanced cubic component to a three-eigenvector. Its exterior rows vanish. If a partial selection has already contributed a signed residual to an exterior row, every remaining selected neighbor contributes a unit in magnitude.

Assign nonnegative weights to the exterior rows. Summing their weighted absolute residuals bounds the required total weighted incidence from the remaining support. A uniform upper bound on the weighted incidence of each remaining vertex then bounds the number of vertices needed. This provides a dual test for partial shell completions in Hong–Wu–Xia Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ExteriorResidualBudget.weighted_exterior_residual_budget`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation](../SupportedEigenSaturation.md)
