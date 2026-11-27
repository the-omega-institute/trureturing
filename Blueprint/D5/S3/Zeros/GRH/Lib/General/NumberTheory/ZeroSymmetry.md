# Zero Symmetry

## Abstract

Zero Symmetry

Symmetry of zeros of Dirichlet L-functions from the functional equation, imprimitive characters included.

**Theorem 1.1 (LFunction_one_sub_eq_zero).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/NumberTheory/ZeroSymmetry.LFunction_one_sub_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/NumberTheory/ZeroSymmetry.LFunction_one_sub_eq_zero` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Symmetry of the zeros: if L(s, χ) = 0, re s ≠ 0 and s ≠ 1, then either s is a pole of the gamma factor of χ (where Mathlib gives it the value 0), or L(1 − s, χ⁻¹) = 0.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/NumberTheory/ZeroSymmetry.LFunction_one_sub_eq_zero`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/SumOverUnits](../Algebra/SumOverUnits.md)
