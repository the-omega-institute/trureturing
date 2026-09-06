# Infinite Sinc Product

## Abstract

Dyadic uniform-interval Fourier factors form a sinc product nonzero off the real axis.

**Theorem 1.1 (The dyadic sinc product is nonzero away from the real axis).**

$$\forall ell \in \operatorname{Real}\left(\right),\; 0 < ell \Rightarrow \left(\left(\left(\left(\forall n \in \operatorname{Natural}\left(\right),\; \left(\left(\left(\left(0 < \operatorname{dyadicHalfWidth}\left(ell, n\right) \land \left(\forall x \in \operatorname{Real}\left(\right),\; 0 \le \operatorname{uniformIntervalDensity}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right), x\right)\right)\right) \land \left(\forall x \in \operatorname{Real}\left(\right),\; \operatorname{uniformIntervalDensity}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right), -x\right) = \operatorname{uniformIntervalDensity}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right), x\right)\right)\right) \land \operatorname{Integrable}\left(\operatorname{uniformIntervalDensity}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right)\right)\right)\right) \land \operatorname{integral}\left(\operatorname{uniformIntervalDensity}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right)\right)\right) = 1\right) \land \left(\forall z \in \operatorname{Complex}\left(\right),\; \operatorname{uniformIntervalFourierLaplace}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right), z\right) = \operatorname{complexSinc}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right) \cdot z\right)\right)\right) \land \operatorname{tsum}\left(\left(\operatorname{dyadicHalfWidth}\left(ell, n\right)\right)_{n \in \operatorname{Natural}\left(\right)}\right) = \frac{ell}{2}\right) \land \left(\forall K \in \operatorname{Set}\left(\operatorname{Complex}\left(\right)\right),\; \operatorname{IsCompact}\left(K\right) \Rightarrow \operatorname{HasProdUniformlyOn}\left((n: \operatorname{Natural}\left(\right), z: \operatorname{Complex}\left(\right) \mapsto \operatorname{complexSinc}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right) \cdot z\right)), (z: \operatorname{Complex}\left(\right) \mapsto \operatorname{tprod}\left(\left(\operatorname{complexSinc}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right) \cdot z\right)\right)_{n \in \operatorname{Natural}\left(\right)}\right)), K\right)\right)\right) \land \left(\forall z \in \operatorname{Complex}\left(\right),\; \operatorname{im}\left(z\right) \ne 0 \Rightarrow \operatorname{tprod}\left(\left(\operatorname{complexSinc}\left(\operatorname{dyadicHalfWidth}\left(ell, n\right) \cdot z\right)\right)_{n \in \operatorname{Natural}\left(\right)}\right) \ne 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/InfiniteSincProduct.dyadic_uniform_convolution_product_ne_zero_off_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive ell, the nth half-width is ell divided by 2^(n+2). Each associated uniform interval density is nonnegative, even, integrable, and has integral one. Its complex Fourier-Laplace transform is the corresponding removable sinc factor.

The half-widths sum to ell/2 and their squares are summable. A quadratic estimate for complex sinc minus one gives uniform convergence of the product on every compact subset of the complex plane.

Every factor is nonzero at a point with nonzero imaginary part. Absolute summability of the factor deviations then prevents the infinite product itself from vanishing there.

This theorem records the interval components, their exact transform factors, and the infinite-product conclusion. It does not construct the limiting convolution density or assert smoothness and decay.

## References

- Truth anchor: `D5/S3/Fourier/InfiniteSincProduct.dyadic_uniform_convolution_product_ne_zero_off_real`
