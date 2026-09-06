# Dyadic Transform Decay

## Abstract

The real-axis transform of the dyadic convolution density has integrable polynomial weights of every natural order.

**Theorem 1.1 (Every polynomial weight is integrable).**

$$\forall ell \in \operatorname{Real}\left(\right),\; 0 < ell \Rightarrow \left(\forall k \in \operatorname{Natural}\left(\right),\; \operatorname{Integrable}\left((xi: \operatorname{Real}\left(\right) \mapsto \operatorname{abs}\left(xi\right)^{k} \cdot \operatorname{norm}\left(\operatorname{densityFourierLaplace}\left(\operatorname{dyadicConvolutionDensity}\left(ell\right), xi\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DyadicTransformDecay.dyadic_density_transform_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transform is the positive-sign Fourier-Laplace integral of the previously constructed density, evaluated at a real frequency. Its frozen identity with the infinite sinc product connects the estimate to that actual density.

Use the decay estimates of orders k and k+2 to bound the corresponding weighted norms outside the unit interval; inside, each sinc factor has norm at most one. Together these give a constant multiple of the integrable function 1/(1+xi^2). Measurability follows from the finite products and their pointwise limit.

This statement supplies weighted integrability. Fourier inversion and infinite differentiability of the density remain outside this module.

**Theorem 1.2 (Arbitrary inverse-power decay).**

$$\forall ell \in \operatorname{Real}\left(\right),\; 0 < ell \Rightarrow \left(\forall k \in \operatorname{Natural}\left(\right),\; \exists C \in \operatorname{Real}\left(\right),\; 0 < C \land \left(\forall xi \in \operatorname{Real}\left(\right),\; 1 \le \operatorname{abs}\left(xi\right) \Rightarrow \operatorname{norm}\left(\operatorname{densityFourierLaplace}\left(\operatorname{dyadicConvolutionDensity}\left(ell\right), xi\right)\right) \le \frac{C}{\operatorname{abs}\left(xi\right)^{k}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DyadicTransformDecay.sinc_product_decay_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Retain the first k factors. Their norms are bounded by 1/(a_j*|xi|), where a_j=ell/2^(j+2) for j starting at zero. Every remaining real-axis factor has norm at most one. Passing the finite-product inequality through the convergent product gives C equal to the product of the first k inverse half-widths. This estimate is the active intermediate result used in the weighted-integrability proof.

## References

- Truth anchor: `D5/S3/Fourier/DyadicTransformDecay.dyadic_density_transform_decay`
- Truth anchor: `D5/S3/Fourier/DyadicTransformDecay.sinc_product_decay_bound`
- Dependency: [D5/S3/Fourier/DyadicConvolutionDensity](DyadicConvolutionDensity.md)
- Dependency: [D5/S3/Fourier/InfiniteSincProduct](InfiniteSincProduct.md)
