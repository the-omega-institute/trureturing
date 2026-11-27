# Crystalline Limit

## Abstract

Crystalline Limit

Dwork's trick: after Frobenius the frame is constant basis times unit over A_max. Uniform denominator for the integral crystalline comparison over A_max, independent of rank. Limit of crystalline representations of bounded weights is crystalline (Liu), group-ring form.

**Theorem 1.1 (isCrystalline_of_trace_limit).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicHodge/Comparison/CrystallineLimit.isCrystalline_of_trace_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicHodge/Comparison/CrystallineLimit.isCrystalline_of_trace_limit` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Limits of crystalline representations. G compact, toGp : Δ → Gp p (from OverGp) of open image, w: Δ → Z_p[G] multiplicative, R continuous with IsTraceNondeg; X finite families of continuous representations, crystalline along w with jumps in [0, h]. If ‖tr R‖ ≤ ε on the kernel in Z_p[G] of some family, for each ε > 0, then R∘w is crystalline.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicHodge/Comparison/CrystallineLimit.isCrystalline_of_trace_limit`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/CrystallinePeriodMatrix](../WachKisin/CrystallinePeriodMatrix.md)
