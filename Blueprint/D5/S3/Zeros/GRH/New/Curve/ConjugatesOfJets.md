# Conjugates Of Jets

## Abstract

Conjugates Of Jets

Standard data: stability, and p-adic bounds transfer from theta products to their jets. Scaled jets of standard theta data are integral at every prime. One theta lift raises valuations by the bound on jets of standard data. Galois conjugation of theta jets as semilinear map on Weil space, with size bounds.

**Theorem 1.1 (exists_semilinear_isJetConjugate).**

Lean statement: `D5/S3/Zeros/GRH/New/Curve/ConjugatesOfJets.exists_semilinear_isJetConjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Curve/ConjugatesOfJets.exists_semilinear_isJetConjugate` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Conjugates of jets. For V standard of rank n, R ∩ R̄ = ∅ and σ ∈ Aut(ℂ/K), there are |t|² = 1/Ω, c ≠ 0, a norm-one finite adele z and a σ-semilinear L such that: for f in 𝒲_f and finite g, σ(T_per f) = T_t(Lf) (places permuted) and Lω(g)f = (σΔ(g)/Δ(g))ω(g)Lf; |Lϱ(αx)ω(g)θ°| ≤ exp(C(N₁n+1)²) everywhere, C = Parameters.c; L(Ψ⊗vac) = cω(z)(σΨ⊗vac) for Ψ Schwartz–Bruhat above R. Here T_a = Space.jetSeries a and per = Parameters.jetScale.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Curve/ConjugatesOfJets.exists_semilinear_isJetConjugate`
- Dependency: [D5/S3/Zeros/GRH/Lib/CM/Reciprocity/SemilinearWeilLaw](../../Lib/CM/Reciprocity/SemilinearWeilLaw.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/TestRings](../../Lib/Cohomology/Etale/TestRings.md)
- Dependency: [D5/S3/Zeros/GRH/New/Curve/IntegralVacuum](IntegralVacuum.md)
