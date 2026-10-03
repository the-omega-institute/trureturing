# Prime Ideal Log Tail

## Abstract

Prime Ideal Log Tail.

**Definition 1.1 (prime Ideal Zeta Sum).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.primeIdealZetaSum`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.primeIdealZetaSum` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Partial Dirichlet series Σ_{𝔭 ∈ S} N𝔭^{-s} over nonzero prime ideals 𝔭 of 𝓞 K lying in the set S.

**Definition 1.2 (Has Dirichlet Density).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.HasDirichletDensity`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.HasDirichletDensity` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The Dirichlet density of a set S of prime ideals of 𝓞 K is δ when the ratio of partial sums tends to δ as s ↓ 1. Sharifi 7.1.13: δ(S) = lim_{s → 1⁺} (Σ_{𝔭 ∈ S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s}).

**Definition 1.3 (Has Lower Dirichlet Density).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.HasLowerDirichletDensity`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.HasLowerDirichletDensity` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Lower Dirichlet density (liminf of the ratio), matching Sharifi's δ_inf notation.

**Theorem 1.4 (Prime Ideal Log Tail).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.abs_tsum_neg_log_one_sub_sub_rpow_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.abs_tsum_neg_log_one_sub_sub_rpow_le` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The remainder Σ_𝔭 (-log(1 - N𝔭^{-s}) - N𝔭^{-s}) is bounded near s = 1 (Sharifi 7.1.12).

## References

- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.HasDirichletDensity`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.HasLowerDirichletDensity`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.abs_tsum_neg_log_one_sub_sub_rpow_le`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/PrimeIdealLogTail.primeIdealZetaSum`
- Dependency: [D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct](NumberFieldEulerProduct.md)
