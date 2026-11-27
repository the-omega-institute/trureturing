# Ribet Element

## Abstract

Ribet Element

Ribet's Hecke element for columns with ties; valuation at the lift within budget.

**Theorem 1.1 (ribet_columns).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/RibetElement.ribet_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/RibetElement.ribet_columns` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Ribet's method. Let u_x be IsLabelledColumn, of trace ψ·row + Σ_{e<t} cyc^{−e} with SelmerLengthLe on 𝓧, with places IsPrimeTriangle, and S, 𝒥 as in IsTraceIdeal, e_j(1) = 1. Then x ↦ det Σ_g ω_g(u_x(g) − 1), ω from ribetNormaliser, satisfies IsRibetElement at π with coefficient d, v(chosenGroupOrder³·d) ≤ |r|·rowBudget.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/RibetElement.ribet_columns`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cyclotomic/OddSha/OddShaBound](../../Lib/Cyclotomic/OddSha/OddShaBound.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/LabelledColumns](LabelledColumns.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/OnePlaceDefect](OnePlaceDefect.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/RowBalanced](RowBalanced.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/TateTwistSteps](TateTwistSteps.md)
