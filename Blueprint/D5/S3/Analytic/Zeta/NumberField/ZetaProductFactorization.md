# Zeta Product Factorization

## Abstract

Zeta Product Factorization.

**Definition 1.1 (artin Dirichlet Series).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization.artinDirichletSeries`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization.artinDirichletSeries` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The Dirichlet series L_χ(s) = ∑'_{𝔞 ≠ ⊥} χ(𝔞) N𝔞^{-s} of a Galois character, as a function of s. This is the analytic engine of Sharifi 7.1.16–7.1.19; for 1 < Re s it equals the Euler product over unramified primes (exists_artinLSeries_eulerProduct_abelian).

**Theorem 1.2 (Zeta Product Factorization).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization.log_norm_ramified_factor_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization.log_norm_ramified_factor_bounded` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

For the Euler product R(s) over prime ideals of L lying above primes ramified in L/K, there is a real C such that |log ‖R(s)‖| ≤ C eventually as real s decreases to one from above. This is the bounded logarithmic ramification correction in the factorisation argument.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization.artinDirichletSeries`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductFactorization.log_norm_ramified_factor_bounded`
- Dependency: [D5/S3/Analytic/Zeta/NumberField/ZetaProductAnalytic](ZetaProductAnalytic.md)
