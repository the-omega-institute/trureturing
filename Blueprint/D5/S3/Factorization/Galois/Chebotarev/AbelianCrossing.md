# Abelian Crossing

## Abstract

Abelian Crossing.

**Theorem 1.1 (Abelian Crossing).**

Lean statement: `D5/S3/Factorization/Galois/Chebotarev/AbelianCrossing.liminf_density_S_sigma_ge_card_H_n_div_GH`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/Chebotarev/AbelianCrossing.liminf_density_S_sigma_ge_card_H_n_div_GH` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Sharifi 7.2.2 Step 2 — partial lower bound on δ_inf(S_σ) coming from one cyclotomic crossing modulus m: |H_n(m)|/(|G|·|H(m)|) bounds the liminf of the density ratio for S_σ in K. Source quote (p. 144): "δ_inf(S_σ) ≥ |H_n|/(|G|·|H|)". The crossing is only valid at *admissible* m, so this per-m bound carries the same two hypotheses as exists_cyclotomicCrossing_fibres: hm4 : m % 4 ≠ 2 (feeding the cyclotomic case) and hcop : ((NumberField.discr L).natAbs).Coprime m (the linear-disjointness via the everywhere-unramified intersection / discr_dvd_discr).

## References

- Truth anchor: `D5/S3/Factorization/Galois/Chebotarev/AbelianCrossing.liminf_density_S_sigma_ge_card_H_n_div_GH`
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/Cyclotomic](Cyclotomic.md)
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/CyclotomicCrossingFibres](CyclotomicCrossingFibres.md)
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/FixedFieldDensity](FixedFieldDensity.md)
