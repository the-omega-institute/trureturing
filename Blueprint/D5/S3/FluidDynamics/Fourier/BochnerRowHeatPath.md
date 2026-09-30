# Bochner Row Heat Path

## Abstract

The projected row-divergence heat kernel gives a continuous Bochner integral path on the full Fourier lattice.

**Theorem 1.1 (Bochner row heat path).**

Lean statement: `D5/S3/FluidDynamics/Fourier/BochnerRowHeatPath.bochner_row_heat_path`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/BochnerRowHeatPath.bochner_row_heat_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive viscosity and a positive closed time interval. Tensor coefficients range over every pair of integer frequencies, with complex two-by-two Frobenius fibres. Let q be a globally continuous tensor-valued square-summable path with a uniform norm bound. At output component i, row divergence contracts the derivative frequency index j with tensor entry q(i,j); the Leray projection then removes the longitudinal part.

The heat multiplier makes this projected row divergence bounded by the inverse square root of positive elapsed time. That singularity is integrable at zero. A measurable full-lattice operator path and dominated convergence therefore give a continuous Hilbert-valued Bochner integral D. The same path satisfies D(0)=0 and, for every t in the closed interval, its norm is at most 2*C*sqrt(t/nu), where C is the stated global bound for q.

For each time in the closed interval and every frequency, coefficient evaluation of this same D is exactly the interval integral from zero to that time of the heat multiplier applied to the projected row divergence of q. The assertion does not supply q as a nonlinear tensor product or establish a fixed point, solution uniqueness, pressure, or smoothness.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/BochnerRowHeatPath.bochner_row_heat_path`
