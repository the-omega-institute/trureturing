# Dyadic Convolution Density

## Abstract

The dyadic convolution limit is a compactly supported probability density with the prescribed infinite sinc transform.

**Theorem 1.1 (The limiting density has the infinite sinc transform).**

$$\forall ell \in \operatorname{Real}\left(\right),\; 0 < ell \Rightarrow \left(\forall z \in \operatorname{Complex}\left(\right),\; \operatorname{densityFourierLaplace}\left(\operatorname{dyadicConvolutionDensity}\left(ell\right), z\right) = \operatorname{tprod}\left((j: \operatorname{Natural}\left(\right) \mapsto \operatorname{complexSinc}\left(\operatorname{dyadicHalfWidth}\left(ell, j\right) \cdot z\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DyadicConvolutionDensity.dyadicConvolutionDensity_fourierLaplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density is the pointwise limit of the finite convolutions of the uniform densities with half-width ell/2^(j+2), starting at j=0. Two components give a Lipschitz density. Subsequent convolution preserves its Lipschitz bound, and adding a component of half-width a changes its value by at most L*a. Summability of the widths proves the Cauchy property.

The accompanying theorems prove nonnegativity, evenness, integrability, integral one, and topological support contained in [-ell/2, ell/2]. A common compactly supported bound passes the integral and the complex Fourier-Laplace transform through the limit by dominated convergence.

The transform uses exp(I*z*x), as do the frozen uniform factors. The finite-convolution identity below identifies the transform limit with the previously frozen sinc product. Smoothness of all orders and polynomial decay are outside this statement.

**Theorem 1.2 (The finite convolution transform bridge).**

$$\forall ell \in \operatorname{Real}\left(\right), n \in \operatorname{Natural}\left(\right), z \in \operatorname{Complex}\left(\right),\; \operatorname{densityFourierLaplace}\left(\operatorname{dyadicPartialConvolution}\left(ell, n\right), z\right) = \operatorname{prod}\left(\operatorname{range}\left(n + 1\right), (j: \operatorname{Natural}\left(\right) \mapsto \operatorname{uniformIntervalFourierLaplace}\left(\operatorname{dyadicHalfWidth}\left(ell, j\right), z\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DyadicConvolutionDensity.dyadic_partial_convolution_fourierLaplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Index n denotes n+1 components, indexed from zero through n. Multiplication by exp(I*z*x) commutes with convolution in the required weighted form. Applying the integral convolution formula and induction gives the finite product, including nonreal z.

## References

- Truth anchor: `D5/S3/Fourier/DyadicConvolutionDensity.dyadicConvolutionDensity_fourierLaplace`
- Truth anchor: `D5/S3/Fourier/DyadicConvolutionDensity.dyadic_partial_convolution_fourierLaplace`
- Dependency: [D5/S3/Fourier/InfiniteSincProduct](InfiniteSincProduct.md)
