# Frame Norm

## Abstract

Frame Norm

Basic properties of frame vectors and the size function modulo the Bessel subgroup. Norm bounds for unitary elements from bounded frames and bounded dual frames.

**Theorem 1.1 (besselSize_le_of_dual).**

Lean statement: `D5/S3/Zeros/GRH/New/RealPlace/FrameNorm.besselSize_le_of_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/RealPlace/FrameNorm.besselSize_le_of_dual` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let V_0, …, V_{2ϱ} have lengths at most M ≥ 1, with V_a = x⁻¹f_{a+1} for a ≤ ϱ, and h(V_a, V_b) = −1 if a+b = 2ϱ, 0 if a+b < 2ϱ. Then besselSize x ≤ 8(ϱ+1)M.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/RealPlace/FrameNorm.besselSize_le_of_dual`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/BesselSystem](../Filling/BesselSystem.md)
