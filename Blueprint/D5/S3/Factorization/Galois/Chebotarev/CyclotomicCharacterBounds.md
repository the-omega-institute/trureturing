# Analytic input of the cyclotomic case (Dirichlet's argument)

## Abstract

Analytic input of the cyclotomic case (Dirichlet's argument).

**Definition 1.1 (twisted Prime Sum).**

Lean statement: `D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds.twistedPrimeSum`

*Formalization.* `D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds.twistedPrimeSum` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The twisted prime sum ∑'_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ over the unramified primes, as a complex function of s. The χ = 1 value is the real prime sum ∑'_𝔭 N𝔭⁻ˢ; the χ ≠ 1 values are bounded near s = 1.

**Theorem 1.2 (Analytic input of the cyclotomic case (Dirichlet's argument)).**

Lean statement: `D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds.artinLSeries_prime_sum_bounded_of_ne_one`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds.artinLSeries_prime_sum_bounded_of_ne_one` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

For a finite abelian cyclotomic Galois extension L/K of modulus m with m ≥ 1 and m % 4 ≠ 2, and a nontrivial Galois character χ, the twisted sum over unramified prime ideals Σ_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ stays bounded as s ↓ 1. Now discharged modulo the complex-analytic bridge: produce the analytic extension Lf (LF4 artinLSeries_analytic_extension, itself ⟸ the geometry-of-numbers leaf character_sum_geometry_of_numbers_bound), note Lf 1 ≠ 0 (LF5 artinLSeries_one_ne_zero), and feed both to artinLSeries_prime_sum_bounded_of_analytic_extension.

## References

- Truth anchor: `D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds.artinLSeries_prime_sum_bounded_of_ne_one`
- Truth anchor: `D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds.twistedPrimeSum`
- Dependency: [D5/S3/Analytic/Zeta/NumberField/ZetaProduct](../../../Analytic/Zeta/NumberField/ZetaProduct.md)
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/CyclotomicNormResidue](CyclotomicNormResidue.md)
