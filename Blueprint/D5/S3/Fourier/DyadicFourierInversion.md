# Dyadic Fourier Inversion

## Abstract

Fourier inversion identifies the dyadic convolution density with a smooth inverse transform.

**Theorem 1.1 (Smoothness of the density).**

$$\forall ell \in \operatorname{Real}\left(\right),\; 0 < ell \Rightarrow \left(\forall k \in \operatorname{Natural}\left(\right),\; \operatorname{ContDiff}\left(\operatorname{Real}\left(\right), k, \operatorname{dyadicConvolutionDensity}\left(ell\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DyadicFourierInversion.dyadicConvolutionDensity_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive width and every natural order k, the previously constructed real density is C^k. This is infinite differentiability. The order is stated with natural numbers because the outer top of the pinned smoothness index denotes analyticity.

Apply Mathlib's weighted-integrability theorem to the transform, compose with negation to obtain its inverse transform, and take the real part. The inversion identity below identifies this smooth function with the actual pointwise convolution limit.

**Theorem 1.2 (Pointwise inversion).**

$$\forall ell \in \operatorname{Real}\left(\right),\; 0 < ell \Rightarrow \left(\forall x \in \operatorname{Real}\left(\right),\; \operatorname{dyadicConvolutionDensity}\left(ell, x\right) = \operatorname{re}\left(\operatorname{fourierInv}\left((xi: \operatorname{Real}\left(\right) \mapsto \operatorname{densityFourierLaplace}\left(\operatorname{dyadicConvolutionDensity}\left(ell\right), -2 \cdot \operatorname{pi}\left(\right) \cdot xi\right)), x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DyadicFourierInversion.dyadic_density_eq_fourier_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fourier-Laplace transform uses the positive exponential exp(i*z*x). Mathlib's Fourier transform uses exp(-2*pi*i*xi*x), so its frequency equals -2*pi*xi in the former convention. The formula uses Mathlib's inverse transform of this rescaled function.

The frozen finite-convolution Lipschitz estimate passes to the pointwise limit and gives continuity. The frozen order-zero weighted integrability, after the frequency substitution, supplies the other hypothesis of Mathlib's Fourier inversion theorem.

## References

- Truth anchor: `D5/S3/Fourier/DyadicFourierInversion.dyadicConvolutionDensity_contDiff`
- Truth anchor: `D5/S3/Fourier/DyadicFourierInversion.dyadic_density_eq_fourier_inversion`
- Dependency: [D5/S3/Fourier/DyadicConvolutionDensity](DyadicConvolutionDensity.md)
- Dependency: [D5/S3/Fourier/DyadicTransformDecay](DyadicTransformDecay.md)
