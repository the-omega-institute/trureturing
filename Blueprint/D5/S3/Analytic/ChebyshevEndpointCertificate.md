# Chebyshev Endpoint Certificate

## Abstract

A shifted Chebyshev filter gives a dimension-free endpoint certificate from actual finite noisy moments.

**Theorem 1.1 (Quadratic endpoint amplification with an explicit noise cost).**

Lean statement: `D5/S3/Analytic/ChebyshevEndpointCertificate.noisy_moment_endpoint_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ChebyshevEndpointCertificate.noisy_moment_endpoint_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r, s and n be natural numbers, let i0 belong to Fin r, and let 0 <= a < b, eta > 0 and epsilon >= 0. Let x and u be real functions on Fin r, and y and v real functions on Fin s. Assume x(i) >= a, a <= y(j) <= b, u(i) >= 0 and v(j) >= 0 for every index, with sum u = sum v = 1. Suppose x(i0) >= b, the sum of u(i) over all indices with x(i)=x(i0) is at least eta, and the absolute difference of the actual Prony moments is at most epsilon for every natural degree k <= n. Then 2 eta n^2 (x(i0)-b) <= (b-a) [2(1-eta)+epsilon Q^n], where Q=2(2+a+b)/(b-a)+1. The proof constructs the affine Chebyshev filter, derives its n^2 exterior growth from a first-difference induction, and propagates the raw-moment noise budget through the recurrence of a modified linear functional. Colliding nodes and zero weights are allowed; the atom mass includes every weight at the same position. No polynomial certificate, spectral separation, or mode-count bound is assumed. This finite-moment estimate does not assert an observation-horizon minimax law.

## References

- Truth anchor: `D5/S3/Analytic/ChebyshevEndpointCertificate.noisy_moment_endpoint_certificate`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](GoldenTomography/FinitePronyHankelReconstruction.md)
