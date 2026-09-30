# Projected heat divergence on the full lattice

## Abstract

The full Fourier heat-divergence multiplier has an inverse-square-root time bound.

**Theorem 1.1 (Projected heat-divergence operator).**

Lean statement: `D5/S3/FluidDynamics/Fourier/HeatProjectedDivergence.heat_projected_divergence_operator`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/HeatProjectedDivergence.heat_projected_divergence_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive viscosity nu and positive elapsed time r, use every frequency in the two-dimensional integer lattice. The source is the square-summable space of complex two-by-two tensor coefficients, and the target is the square-summable space of complex two-vector coefficients. Both are unweighted lp spaces; in the H2 application, their inputs are already multiplied by one plus the squared frequency. The theorem constructs a continuous complex-linear operator whose coefficient at k is the heat factor exp(-nu*r*|k|^2) times the imaginary unit, the Leray orthogonal projection, and contraction of the tensor at k with the frequency vector.

For every tensor input, the output norm is at most (nu*r)^(-1/2) times its input norm. This includes the zero mode, where the frequency contraction vanishes. The proof bounds contraction by |k|, uses that the projection is an orthogonal contraction, then applies the Gaussian inequality |k| exp(-nu*r*|k|^2) <= (nu*r)^(-1/2) uniformly over the full lattice. The coordinate operators assemble into a bounded lp map.

This is a fixed positive-time multiplier estimate. It does not construct a time integral, prove continuity at r=0, build a mild path, or prove the original Recovery 25.3 or 25.4 conclusions.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/HeatProjectedDivergence.heat_projected_divergence_operator`
- Dependency: [D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution](WeightedTensorConvolution.md)
