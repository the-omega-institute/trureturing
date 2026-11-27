# Kummer Chart Exists

## Abstract

Kummer Chart Exists

Weil pairs (s, m): products, powers, uniqueness of m. Embedding of W(F_q) into algebraic closure of Q_p via θ; fixers agree. Action of Frobenius and Galois group on A_inf, W(C^♭); Teichmüller roots of unity. Every p-adic field has a Kummer chart from a uniformiser and its root tower.

**Theorem 1.1 (exists_kummer_chart).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/KummerChartExists.exists_kummer_chart`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/KummerChartExists.exists_kummer_chart` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

If j(Γ) is open, there is a chart over Λ = W(F_{p^f}) with ef = [G_p : j(Γ)] such that j(Γ) fixes Λ and θ(z), contains the fixer of θ(S), a p^f-Frobenius and elements with gz = [ε]^l z for all l ≥ 0; e = 1, E = z + p if j(Γ) contains inertia.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/KummerChartExists.exists_kummer_chart`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/Main/LocalEmbedding](../../GaloisRep/Main/LocalEmbedding.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/NumberTheory/Valuation](../../General/NumberTheory/Valuation.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/PeriodMatrixBasis](PeriodMatrixBasis.md)
