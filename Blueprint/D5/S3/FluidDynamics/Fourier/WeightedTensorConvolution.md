# Weighted Tensor Convolution

## Abstract

Quadratic weighted tensor convolution on the integer lattice has norm bound sixteen.

**Definition 1.1 (weight).**

Lean statement: `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.weight`

*Formalization.* `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quadratic Fourier weight on the two-dimensional integer lattice.

**Definition 1.2 (outer).**

Lean statement: `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.outer`

*Formalization.* `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.outer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex outer product uses the Euclidean tensor fibre, hence the Frobenius norm.

**Definition 1.3 (convolution).**

Lean statement: `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.convolution`

*Formalization.* `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.convolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient convolution sums over every lattice frequency.

**Theorem 1.4 (weighted tensor convolution).**

Lean statement: `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.weighted_tensor_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.weighted_tensor_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex vector coefficients with summable quadratic weighted energies, each tensor convolution converges absolutely, its weighted energy is summable, and the square root of that energy is at most sixteen times the product of the two input energy square roots.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.convolution`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.outer`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.weight`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.weighted_tensor_convolution`
