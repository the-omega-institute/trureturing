# Open Cell Bound

## Abstract

Open Cell Bound

Mean-square bound for Bessel integrals on the open cell.

**Theorem 1.1 (open_cell).**

Lean statement: `D5/S3/Zeros/GRH/New/RealPlace/OpenCellBound.open_cell`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/RealPlace/OpenCellBound.open_cell` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Open-cell bound. For ρ ≥ B, 𝗀(Z(γ)) > 0, Box(ρ) meeting γBox(ρ): there are compact A, random t ∈ 𝖴⁰H and n of mass ≤ cellMass with 𝔼‖∫_A φ(y) W(γty)W(ty)* dy‖² ≤ ∫|φ|² dn; almost surely A contains the y ∈ Box(ρ) with R(γty) ≤ ρ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/RealPlace/OpenCellBound.open_cell`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/StableCells](../Filling/StableCells.md)
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/SobolevCell](SobolevCell.md)
