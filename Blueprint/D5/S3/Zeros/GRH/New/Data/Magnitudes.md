# Magnitudes

## Abstract

Magnitudes

Logarithmic size calculus (upper and lower exponent bounds) for the parameters of the data.

**Theorem 1.1 (roundUp_mem_Icc).**

Lean statement: `D5/S3/Zeros/GRH/New/Data/Magnitudes.roundUp_mem_Icc`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Data/Magnitudes.roundUp_mem_Icc` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

If the real number F satisfies exp(l) ≤ F for some real l, so that F > 0, then the rounded value N₁⌈F/N₁⌉ (Data.roundUp) lies in the closed interval [F, F + N₁].

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Data/Magnitudes.roundUp_mem_Icc`
- Dependency: [D5/S3/Zeros/GRH/New/Data/AdmissibleData](AdmissibleData.md)
