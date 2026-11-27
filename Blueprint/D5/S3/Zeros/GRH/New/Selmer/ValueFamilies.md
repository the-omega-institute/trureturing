# Value Families

## Abstract

Value Families

Group-ring interpolation of twisted Hecke values, carried to the Galois side as families.

**Theorem 1.1 (exists_isFamily).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/ValueFamilies.exists_isFamily`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/ValueFamilies.exists_isFamily` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For chosen w ∤ ℓ with tame generator σ, ramified p and a sign s, some family (ν, L) (IsFamily) has all v(ν_i(σ) − 1) ≤ v(Nw − 1), and vL(Q, avatar of τ⁻¹) ≤ c + vL(∅,1) implies v(ιρ) ≤ c, for c ≥ 0, twists τ with Q auxiliary, ρ = Data.Pair.ratio p τ s.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/ValueFamilies.exists_isFamily`
- Dependency: [D5/S3/Zeros/GRH/New/Rows/Carrier](../Rows/Carrier.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/AptTuples](AptTuples.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/Corepresentable](Corepresentable.md)
