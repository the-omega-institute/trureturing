# Finite System

## Abstract

Finite System

One-sided Siegel formula at T; top kernel dominates phase sums nearly sharply. Finite places carry a local system with sharp bottom value and frequency bounds.

**Theorem 1.1 (exists_finite_sieveSystem).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/FiniteSystem.exists_finite_sieveSystem`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/FiniteSystem.exists_finite_sieveSystem` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let 1/g be integral off T. Some K(g) ≤ Z ≤ K contains k_T whenever k ∈ K reduces into Filling.fixingSet Sg d, and for every compact open subgroup L the normalised forms Level.floorForm, Level.topKernel of Z form a SieveSystem with bottom bound (1 + b⁻⁶)/b^(6|κ||Sg|).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/FiniteSystem.exists_finite_sieveSystem`
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/OneVector/OneVector](../../Lib/SiegelWeil/OneVector/OneVector.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/FixedLines](FixedLines.md)
