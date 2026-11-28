# Twist For Rows

## Abstract

Twist For Rows

One anticyclotomic twist makes all Selmer groups short. For finitely many irreducible blocks of Galois representations of lifts, one finite-order anticyclotomic twist ramified at new primes makes, for each of its first m powers, all Selmer groups modulo a given power of ℓ short and the ratios of twisted to untwisted Hecke values barely divisible by ℓ, which limits congruences. Twists of ℓ-power order at new primes that kill a Selmer group or keep L-values barely divisible are known. Related work: Mazur–Rubin, Diophantine stability, 2018; Kriz–Nordentoft, Horizontal p-adic L-functions, 2023; Hida, Non-vanishing modulo p of Hecke L-values, 2004.

**Theorem 1.1 (exists_mFoldTwist_selmerLengthLe).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/TwistForRows.exists_mFoldTwist_selmerLengthLe`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/TwistForRows.exists_mFoldTwist_selmerLengthLe` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For finitely many rows R_i and M, some m-fold twist has, for its first m powers ϑ, ψ the avatar of ϑ⁻¹: Q auxiliary, ψ anticyclotomic, Σ v(ψ(γ) − 1) ≤ cr_ℓ over tame generators γ at Q, Selmer length of ψR_i mod ℓ^M ≤ (10f·rank + 1)cr_ℓ, v(ιρ_p(ϑ^{±1})) ≤ 9cr_ℓ for ramified p. Here cr_ℓ = crudeUnit and ρ_p = Data.Pair.ratio p.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/TwistForRows.exists_mFoldTwist_selmerLengthLe`
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/RowBalanced](RowBalanced.md)
