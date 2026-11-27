# Bessel Schur Bound

## Abstract

Bessel Schur Bound

Definitions: convolution, Bessel functions, unitary action of U(κ). Schur orthogonality: convolution with reproduced functions is an isometry up to the degree.

**Theorem 1.1 (lintegral_sq_convolve_convolve_le).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BesselSchurBound.lintegral_sq_convolve_convolve_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BesselSchurBound.lintegral_sq_convolve_convolve_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Under the hypotheses of IsBoundedMeasurable.lintegral_sq_convolve, for integrable φ the function y ↦ ∫φ(a)(F*x)(ya)da has squared L²(ν) norm at most (‖x‖₂²/d)·(‖F‖²_ν/d)·‖φ‖₂².

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BesselSchurBound.lintegral_sq_convolve_convolve_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bessel/UnipotentCoords](../Bessel/UnipotentCoords.md)
