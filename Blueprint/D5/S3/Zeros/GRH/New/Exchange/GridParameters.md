# Grid Parameters

## Abstract

Grid Parameters

Index sets, signs, parameters of grids and triangles; gaps, interlacing and matching.

**Theorem 1.1 (paramsCorrespond_grid).**

Lean statement: `D5/S3/Zeros/GRH/New/Exchange/GridParameters.paramsCorrespond_grid`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Exchange/GridParameters.paramsCorrespond_grid` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Every step of either grid is an edge (ParamsCorrespond): from (i,j) to (i+1,j) with both parameters negated, or to (i,j+1) with them unchanged, provided the target indices i', j' are at most m and o = 0 or i' = 0.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Exchange/GridParameters.paramsCorrespond_grid`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Lift/Edge](../../Lib/Weil/Lift/Edge.md)
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/IndexTypes](../Seesaw/IndexTypes.md)
