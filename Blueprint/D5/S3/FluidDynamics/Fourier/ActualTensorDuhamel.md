# Actual Tensor Duhamel

## Abstract

Continuous weighted full-frequency tensor products yield an actual projected Bochner Duhamel path.

**Theorem 1.1 (Continuous weighted tensor Duhamel path).**

Lean statement: `D5/S3/FluidDynamics/Fourier/ActualTensorDuhamel.continuous_weighted_tensor_duhamel`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/ActualTensorDuhamel.continuous_weighted_tensor_duhamel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive viscosity and interval length, take two continuous paths of weighted square-summable complex two-vector coefficients over every integer-pair frequency. Assume their norms on the closed interval are bounded by nonnegative Mx and My. At each time, remove the quadratic Fourier weight from both inputs, take the full tensor convolution with row index from the first input and derivative index from the second, and restore the output weight. Every full-lattice outer-product coefficient series is absolutely summable in tensor norm and at each row and derivative-index coefficient, and is summable as a tensor series. The result is an actual continuous square-summable tensor path q whose norm is at most 16 Mx My. For every comparison pair z,w, there exists a square-summable tensor r with exactly the same weighted full-lattice convolution formula. Throughout the closed interval it satisfies the bilinear difference estimate norm(q(t)-r) at most 16 norm(x(t)-z) norm(y(t)) plus 16 norm(z) norm(y(t)-w). The estimate also holds for every square-summable r with that coefficient formula.

Clamp that tensor path to the closed interval and apply the full-lattice projected row-divergence heat operator. This produces one continuous Hilbert-valued path D with D(0)=0 and norm at most 32 Mx My sqrt(t/nu) throughout the original interval. For every frequency and interval time, evaluation of this same D is exactly the Bochner coefficient integral of the heat multiplier, the Leray projection, and the row contraction sum over the derivative index j of kappa_j q(i,j). The same output is fixed by the Leray projection at every frequency, because that projection commutes with the continuous coefficient integral and is idempotent. Its spatial zero-frequency coefficient is zero because the row-divergence multiplier vanishes there.

The theorem does not assert real symmetry, a heat-orbit fixed point, uniqueness, pressure, time differentiability, smoothness, or continuation. Those require further proof for the original prepared paths.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/ActualTensorDuhamel.continuous_weighted_tensor_duhamel`
- Dependency: [D5/S3/FluidDynamics/Fourier/BochnerRowHeatPath](BochnerRowHeatPath.md)
- Dependency: [D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution](WeightedTensorConvolution.md)
