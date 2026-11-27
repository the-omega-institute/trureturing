# Cell Neighbourhood

## Abstract

Cell Neighbourhood

Jacobian and injectivity of the open-cell double coset chart of U(p,q). Explicit perturbation bounds for determinant, inverse and discriminant near an open-cell matrix.

**Theorem 1.1 (mem_openCell_and_bounds_of_near).**

Lean statement: `D5/S3/Zeros/GRH/New/RealPlace/CellNeighbourhood.mem_openCell_and_bounds_of_near`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/RealPlace/CellNeighbourhood.mem_openCell_and_bounds_of_near` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let M ≥ 8(ϱ+1), 𝗀(Z) ≥ M⁻¹, all |Z_ab| ≤ M², P ≥ M^{9(ϱ+1)} and ‖Z' − Z‖ < P⁻⁶. Then 𝗀(Z') ≥ 𝗀(Z)/2, Z' lies in Ω (Shape.openCell), and ‖Z'⁻¹‖, ‖Z'‖, δ(Z')^{−1/2} ≤ P, with δ = cornerDefect.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/RealPlace/CellNeighbourhood.mem_openCell_and_bounds_of_near`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bessel/BesselNormInvariance](../../Lib/DiscreteSeries/Bessel/BesselNormInvariance.md)
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/GramSection](GramSection.md)
