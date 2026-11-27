# Polar Landau

## Abstract

Polar Landau

Landau's lemma for one-sided bounds; Laplace transforms of powers; logarithmic derivatives of L-functions.

**Theorem 1.1 (landau).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Analytic/Landau/PolarLandau.landau`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Analytic/Landau/PolarLandau.landau` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Landau's lemma. Let E satisfy IsPolar with residues r, and let β > 0. If re r(x) ≥ 0 for all real x > β and E(v) ≤ e^{(β−1)v} for large v, then r(ρ) = 0 whenever re ρ > β.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Analytic/Landau/PolarLandau.landau`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/NumberTheory/QuadFieldSplitting](../../General/NumberTheory/QuadFieldSplitting.md)
