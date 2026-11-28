# Lift Volume Height

## Abstract

Lift Volume Height

Height bound for untwisted over twisted volume of one lift on good forms.

**Theorem 1.1 (heightLe_liftVolume_ratio).**

Lean statement: `D5/S3/Zeros/GRH/New/Rows/LiftVolumeHeight.heightLe_liftVolume_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Rows/LiftVolumeHeight.heightLe_liftVolume_ratio` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For m-fold twists θ(ι) satisfying Data.IsFitFamily and 1 ≤ j ≤ m, the volume ratios λ_j(1)/λ_j(θ(ι)^j) (Data.liftVolume) have height (HeightLe) at most d·k·(B₀·log b − 𝖴), with d the dimension of Data.rows and 𝖴 = Data.dirCost (size of a jet less its forced divisibility), B₀ = fa(log b)³/(mk) = Data.B₀.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Rows/LiftVolumeHeight.heightLe_liftVolume_ratio`
- Dependency: [D5/S3/Zeros/GRH/New/Rows/ComparisonForms](ComparisonForms.md)
- Dependency: [D5/S3/Zeros/GRH/New/Rows/HeckeValueHeight](HeckeValueHeight.md)
