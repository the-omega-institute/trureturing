# Density of a finite set of primes is 0

## Abstract

Density of a finite set of primes is 0.

**Theorem 1.1 (Density of a finite set of primes is 0).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/Density.hasDirichletDensity_of_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/NumberField/Density.hasDirichletDensity_of_finite` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Density of a finite set of primes is 0 (Sharifi 7.1.13). The numerator Σ_{𝔭 ∈ S} N𝔭^{-s} is bounded (finitely many terms, each ≤ 1) while the denominator Σ_𝔭 N𝔭^{-s} → ∞, so the ratio → 0.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/Density.hasDirichletDensity_of_finite`
- Dependency: [D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct](NumberFieldEulerProduct.md)
- Dependency: [D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail](PrimeIdealLogTail.md)
