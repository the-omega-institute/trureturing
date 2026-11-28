# Degree Bounds

## Abstract

Degree Bounds

Last step: pairing on the top group is a multiple of the branching restriction. Bounds on the Bessel degree of the filling and on the number of Bessel coordinates.

**Theorem 1.1 (log_filling_besselDegree_mem_Icc).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/DegreeBounds.log_filling_besselDegree_mem_Icc`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/DegreeBounds.log_filling_besselDegree_mem_Icc` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

With deg the degree Filling.besselDegree of Data.filling and w = Data.nominalWeight, the number log deg + f Σ_{k−1 ≤ l < r} log l! lies between m(k−1) Σ_v log w(v) and mr Σ_v (log w(v) + 1/x), v over the f infinite places.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/DegreeBounds.log_filling_besselDegree_mem_Icc`
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/BesselGeneric](../Seesaw/BesselGeneric.md)
