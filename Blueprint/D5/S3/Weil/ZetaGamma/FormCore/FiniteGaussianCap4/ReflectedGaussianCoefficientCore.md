# The actual reflected Gaussian coefficient core

## Abstract

Actual three-point reflected Gaussian sources generate the weighted central-charge coefficient kernel.

**Theorem 1.1 (The literal source [1,1,-2] at [a,-a,0]).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianCoefficientCore.actual_reflected_gaussian_coefficient_core`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianCoefficientCore.actual_reflected_gaussian_coefficient_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put z(n)=normalizedCentralMellin(2n)/normalizedCentralMellin(0), N(n)=centralNormalization(n), a(t)=log((1+sqrt(t))/(1-sqrt(t)))/2. Let d(t,n) be the repository's actual finiteGaussianNormalizedCoefficient of the source [1,1,-2] at [a(t),-a(t),0], evaluated at 2n and divided by 2*gaussianSiteAmplitude(a(t)). On 0<t<1/36 these coefficients have a genuine l2 carrier f(t,n)=(n+1)^2*d(t,n), and their closed real span is exactly ker inner(z(n)/(n+1)^2, -).

The actual normalization recurrence supplies inverse coefficient growth; the existing central Mellin weight recurrence gives |z(n)|<=1. The existing atom reflection formulas give d(t,n)=t^n/N(2n) for n>=1, and the actual finite-source central mass HasSum fixes coordinate zero. This proof does not assume a Gaussian expansion, density, or Laguerre completeness. Physical synthesis, continuity of the required energy forms, and identification with any original Suzuki admissible domain remain separate obligations; no RH statement is concluded.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianCoefficientCore.actual_reflected_gaussian_coefficient_core`
- Dependency: [D5/S3/Analytic/PowerSeries/WeightedChargeKernelCore](../../../../Analytic/PowerSeries/WeightedChargeKernelCore.md)
