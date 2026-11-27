# Schur Test

## Abstract

Schur Test

Energy of terms of the second moment; splitting; passage to cut Bessel functions. Size function of a class of terms; open-cell mass fits under it.

**Theorem 1.1 (lintegral_boxCutoff_le_of_average).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/SchurTest.lintegral_boxCutoff_le_of_average`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/SchurTest.lintegral_boxCutoff_le_of_average` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Averaging: let s map (X, m) measurably to 𝖴⁰_∞, B ⊆ X with m(B) ≥ 1, F ≥ 0 be measurable and left 𝖴⁰_c(g)-invariant, ∫_B F(u·s(x)·y)dm ≤ C for u ∈ 𝖴⁰_∞, y ∈ Filling.boxedPoints. Then ∫β⁰_c∏_v‖W_v‖²F ≤ C·ν·#Filling.BesselCoord, for W_v cut, β⁰ = Filling.boxCutoff.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/SchurTest.lintegral_boxCutoff_le_of_average`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/AmplitudeSums](AmplitudeSums.md)
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/VolumeKernel](../RealPlace/VolumeKernel.md)
