# Ordinary-prime triangles on power windows

## Abstract

The ordinary-prime triangle characterizes RH on arbitrarily late power windows.

**Theorem 1.1 (One lower bound on arbitrarily late windows).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTrianglePowerWindow.rh_iff_frequently_prime_triangle_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTrianglePowerWindow.rh_iff_frequently_prime_triangle_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any real b > 1. The Riemann hypothesis is equivalent to the existence of one C ≥ 0 such that, for arbitrarily large X, the ordinary-prime triangle sum is at least 2x log 2 − C√x at every real x in [X, Xᵇ].

For the converse, the filtered Laplace transform retains a nonzero residue at a zero off the critical line. A complex disk isolating a pole and a zero-free disk at its real projection separate the high Taylor coefficients. Gamma weights concentrate the corresponding signed moments in the logarithmic image of the power window. The prime-power error is bounded by a fixed multiple of √x. An off-line zero therefore forces a violation of the lower bound in every sufficiently late window.

The use of localized oscillation has the classical precedent of Kaczorowski and Pintz, Oscillatory properties of arithmetical functions II (1987), DOI 10.1007/BF01951008.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTrianglePowerWindow.rh_iff_frequently_prime_triangle_lower`
- Dependency: [D5/S3/Analytic/Laplace/CriticalGammaWindow](../../../Analytic/Laplace/CriticalGammaWindow.md)
- Dependency: [D5/S3/Analytic/Laplace/EulerPoleObstruction](../../../Analytic/Laplace/EulerPoleObstruction.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne](CompleteMangoldtAtOne.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeQuarterTriangle](PrimeQuarterTriangle.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLaplace](PrimeTriangleLaplace.md)
- Dependency: [D5/S3/Weil/ZetaBridge/EqualRadiusZeroDisks](../../ZetaBridge/EqualRadiusZeroDisks.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../ZetaBridge/RightHalfStripRiemannReduction.md)
