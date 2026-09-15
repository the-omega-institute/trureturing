# Explicit Complex Decay of the Dyadic Transform

## Abstract

The Fourier-Laplace transform of the dyadic convolution density has inverse-power decay of every natural order, with an explicit finite constant and exponential growth controlled by the imaginary part.

**Theorem 1.1 (An explicit bound at every complex frequency).**

$$\forall ell \in \operatorname{Real}\left(\right),\; 0 < ell \Rightarrow \left(\forall k \in \operatorname{Natural}\left(\right), z \in \operatorname{Complex}\left(\right),\; \operatorname{norm}\left(\operatorname{densityFourierLaplace}\left(\operatorname{dyadicConvolutionDensity}\left(ell\right), z\right)\right) \le \frac{\operatorname{exp}\left(\frac{ell \cdot \operatorname{abs}\left(\operatorname{im}\left(z\right)\right)}{2}\right) \cdot \prod_{j \in \operatorname{range}\left(k\right)} (1 + \frac{1}{\operatorname{dyadicHalfWidth}\left(ell, j\right)})}{\left(1 + \operatorname{norm}\left(z\right)\right)^{k}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DyadicComplexDecay.dyadic_transform_explicit_strip_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transform uses the kernel exp(i z x). The half-width with index j is ell divided by 2 to the power j+2, starting with ell/4. Their sum is ell/2. The density transform equals the infinite product of the corresponding complex sinc factors, with the removable value at zero equal to one.

For a positive half-width, the uniform probability integral bounds the factor norm by exp(a abs(Im z)). The exponential formula for sine also bounds the factor norm times norm(z) by exp(a abs(Im z))/a. Adding these inequalities gives the factor bound with numerator exp(a abs(Im z)) times (1+1/a) and denominator 1+norm(z).

Apply the inverse-power bound to the first k factors. Normalize all other factors by their exponential bounds, so their norms are at most one. The total half-width bounds the combined exponential, and convergence of the finite products passes the inequality to the density transform.

The denominator is positive at every frequency. For order zero the finite product is empty and equals one, giving the exponential bound alone. Restricting the imaginary part to any bounded interval makes the exponential uniform there.

## References

- Truth anchor: `D5/S3/Fourier/DyadicComplexDecay.dyadic_transform_explicit_strip_decay`
- Dependency: [D5/S3/Fourier/DyadicConvolutionDensity](DyadicConvolutionDensity.md)
