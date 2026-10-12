# An entire endpoint profile with factorial derivative budgets

## Abstract

A positive integral recurrence bounds every derivative of an entire squared-sinc endpoint profile.

**Definition 1.1 (The entire cosine square-root extension).**

Lean statement: `D5/S3/Analytic/SincSquareDerivativeBudget.psi`

*Formalization.* `D5/S3/Analytic/SincSquareDerivativeBudget.psi` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Maclaurin Series for Trigonometric Functions*. URL: <https://dlmf.nist.gov/4.19>.

*Commentary.*

For every real t, psi(t) is the everywhere convergent series sum_k (-1)^k t^k/(2k)!. For t >= 0 it equals cos(sqrt(t)), including psi(0)=1. The series defines the function also for negative t.

**Definition 1.2 (The entire endpoint profile).**

Lean statement: `D5/S3/Analytic/SincSquareDerivativeBudget.endpoint`

*Formalization.* `D5/S3/Analytic/SincSquareDerivativeBudget.endpoint` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Maclaurin Series for Trigonometric Functions*. URL: <https://dlmf.nist.gov/4.19>.

*Commentary.*

For every real eta and t, endpoint(eta,t) is the series sum_k 2(-1)^k(8/eta)^k t^k/(2k+2)!. Real division is total; the estimates below require eta > 0. For positive t and eta it equals 2[1-cos(sqrt(8t/eta))]/(8t/eta), or sinc(sqrt(2t/eta)) squared.

**Theorem 1.3 (One profile satisfies all endpoint constraints).**

Lean statement: `D5/S3/Analytic/SincSquareDerivativeBudget.endpoint_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SincSquareDerivativeBudget.endpoint_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2026). *Maclaurin Series for Trigonometric Functions*. URL: <https://dlmf.nist.gov/4.19>.

*Commentary.*

For every eta > 0, endpoint eta is infinitely differentiable on the entire real line, has value 1 at zero, is nonnegative for every t >= 0, and is at most eta/2 for every t >= 1. Simultaneously, for every natural n and every t >= 0, |D^n endpoint(eta,t)|/n! <= (8/eta)^n/(2n)!. The recurrence D^(n+1) psi(t) = -(1/2) integral_0^1 r^(2n) D^n psi(r^2 t) dr preserves the oscillatory cancellation; its kernel mass gives n!/(2n)!. The triangular cosine integral then transfers that budget to the endpoint profile.

## References

- Truth anchor: `D5/S3/Analytic/SincSquareDerivativeBudget.endpoint`
- Truth anchor: `D5/S3/Analytic/SincSquareDerivativeBudget.endpoint_budget`
- Truth anchor: `D5/S3/Analytic/SincSquareDerivativeBudget.psi`
- Dependency: [D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay](../FluidDynamics/Fourier/PeriodicAllenCahnDecay.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage](../Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage.md)
