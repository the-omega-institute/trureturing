# Cancellation at an empty first-axis fibre

## Abstract

Cancellation at an empty Q9 fibre

**Theorem 1.1 (The paired Huang sum requires singletons in both layers).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EmptyFibreCancellation.paired_residual_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EmptyFibreCancellation.paired_residual_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a balanced cubic induced support with both lifts of a transverse row outside the support. The full Huang eigen-equation vanishes at both lifts. The first-axis entries vanish there, leaving the negative and positive transverse Huang blocks on the false and true layers, respectively.

The positive first-axis edges give equal switching signs on the two lifts of each paired neighbour. If k neighbours are paired and d is their signed transverse sum, each layer's singleton sum must be -d. Each singleton contributes a unit sign, and the paired and two singleton direction sets share the eight available directions. Hence k + 2|d| is at most eight.

The signed sum is an integer of parity k and magnitude at most k. Combining these facts gives |d| at most two. In particular three paired contacts at an empty row cannot all have the same sign. This is a local constraint for Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EmptyFibreCancellation.paired_residual_bound`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation](../SupportedEigenSaturation.md)
