# Quantitative boundary estimates

## Abstract

Piecewise affine Fourier weights bound the oscillatory integral of the regular part.

**Theorem 1.1 (A uniform bound for the regular boundary integral).**

Lean statement: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/BoundaryEstimate.boundary_regular_integral_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/BoundaryEstimate.boundary_regular_integral_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a spectrum with logarithmic counting asymptotics and paired Laplace data of growth degree k, there is a positive A such that every admissible kernel of positive bandwidth b, M at least four and y at least one has regular boundary integral of norm at most A*(1+b)*M^(max(k,1))/y. The constant is independent of the kernel, bandwidth, cutoff and translation.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/BoundaryEstimate.boundary_regular_integral_bound`
- Dependency: [D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity](DampedIdentity.md)
