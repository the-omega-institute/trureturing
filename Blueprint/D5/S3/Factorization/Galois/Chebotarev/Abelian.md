# Chebotarev's theorem, abelian case

## Abstract

Chebotarev's theorem, abelian case.

**Theorem 1.1 (Chebotarev's theorem, abelian case).**

Lean statement: `D5/S3/Factorization/Galois/Chebotarev/Abelian.chebotarev_abelian`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/Chebotarev/Abelian.chebotarev_abelian` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Chebotarev's theorem, abelian case (Sharifi 7.2.2 Step 2). For an abelian Galois extension L/K of number fields and any σ ∈ Gal(L/K), the Dirichlet density of primes 𝔭 of 𝓞 K unramified in L whose Frobenius equals σ is 1 / |Gal(L/K)|. Composition: the |G| fibres S_σ each have liminf ≥ 1/|G| (liminf_ratio_ge_inv_card_G) and their density ratios sum to 1 (ratioSum_frobeniusFibres_tendsto_one); the pigeonhole glue tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one forces each to the limit 1/|G|.

## References

- Truth anchor: `D5/S3/Factorization/Galois/Chebotarev/Abelian.chebotarev_abelian`
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/AbelianCrossing](AbelianCrossing.md)
