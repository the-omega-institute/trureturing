# Absolute convergence from a one-sided bound

## Abstract

Local continuation at real cuts and an exponential upper bound extend absolute Laplace convergence.

**Theorem 1.1 (Excluding a real abscissa to the right of the bound).**

Lean statement: `D5/S3/Analytic/Laplace/PositiveWindowObstruction.integrable_and_analytic_of_eventually_le_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PositiveWindowObstruction.integrable_and_analytic_of_eventually_le_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be a real function on (U,∞) such that exp(−xt)g(t) is integrable for every x>0. Suppose g(t)≤C exp(σt) for all sufficiently large t, with σ<0 and C real. For each real c with σ<c≤0, assume that if the weighted integrals converge absolutely for x>c and the tail transform is holomorphic on Re(z)>c, then the transform extends holomorphically to a disk centered at c, agreeing on its right half.

Then exp(−xt)g(t) is integrable for every x>σ and the actual tail Laplace transform is holomorphic on Re(z)>σ. For a sufficiently late nonnegative cutoff V, the density C exp(σt)−g(t) on (V,∞) defines a positive measure. Any failed convergence at x>σ would give that measure a real abscissa c∈(σ,0]. The explicit transform of the exponential and the entire finite head would carry the hypothesized extension across c over to the positive Laplace transform, contradicting its singularity at the abscissa.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/PositiveWindowObstruction.integrable_and_analytic_of_eventually_le_exp`
- Dependency: [D5/S3/Analytic/Laplace/EulerPoleObstruction](EulerPoleObstruction.md)
