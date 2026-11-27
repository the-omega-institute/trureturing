# Floor Kernels

## Abstract

Floor Kernels

Laws of floor kernels; pairing on one floor is integral of next floor's pairings.

**Theorem 1.1 (pivotModulus_sq_le).**

Lean statement: `D5/S3/Zeros/GRH/New/RealPlace/FloorKernels.pivotModulus_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/RealPlace/FloorKernels.pivotModulus_sq_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Cauchy–Schwarz on floor l, for a kernel k (Level.IsPairingKernel). If |k_{l+1}(σg, σy)|² ≤ u(σg)v(σ) on H_l, with u, v measurable and u of mass ≤ K on near points (Level.FloorMassLe), then (∫|k_{l+1}(σg, σy)| dθ_l)² ≤ K ∫ v dθ_l.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/RealPlace/FloorKernels.pivotModulus_sq_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/CircleMean](../../Lib/DiscreteSeries/CuspKernel/CircleMean.md)
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/FlatCharts](FlatCharts.md)
