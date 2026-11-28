# Restriction Lemma

## Abstract

Restriction Lemma

Period of deep-level Poincaré series equals main term up to explicit error. Explicit lower bound for oscillating integral of two coefficients over a subgroup. Cauchy matrix of controlled size at which the phases of a restriction period cancel.

**Theorem 1.1 (exists_isTwoFactor_restriction).**

Lean statement: `D5/S3/Zeros/GRH/New/DiscreteSeries/RestrictionLemma.exists_isTwoFactor_restriction`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/DiscreteSeries/RestrictionLemma.exists_isTwoFactor_restriction` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let l, l' satisfy IsSteep for X, B ≥ 1 and M, M+1, with M even and l' of some gap. Some ω in U(diag(ε) ⊕ 1) has ‖ω‖ ≤ (n+1)²(6B)^{2M+1}, and j(r) = (r, ω⁻¹(r ⊕ 1)ω) satisfies IsTwoFactor for l, −l', with phase HCParam.phase zero and second component of j(r) − 1 equal to ω⁻¹((r−1) ⊕ 0)ω.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/DiscreteSeries/RestrictionLemma.exists_isTwoFactor_restriction`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/ModularDataDecay](../../Lib/Weil/DualPair/ModularDataDecay.md)
- Dependency: [D5/S3/Zeros/GRH/New/DiscreteSeries/TwoFactorSetup](TwoFactorSetup.md)
