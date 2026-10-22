# Complete Low-Height Gaussian Moment

## Abstract

The normalized cubic Gaussian moment is an exact identity for every complex parameter.

The normalized Gaussian has center 16*m and variance 2*m. Transport from the Gaussian probability measure proves integrability of every tilted monomial. The entire complex MGF and its first three derivatives evaluate the four density moments needed for the cubic polynomial.

The linear combination of those moments gives the exact covariance correction +2*z. This identity supplies the physical full-line moment for the countable weighted mean, with arbitrary real gamma and arbitrary complex exponential tilt.

**Theorem 1.1 (Exact normalized cubic Gaussian moment).**

$$\forall m \in \mathbb{R},\; \forall gamma \in \mathbb{R},\; \forall z \in \mathbb{C},\; 0 < m \Rightarrow \operatorname{integral}\left(y, \mathbb{R}, \operatorname{ofReal}\left(\frac{\left(y + 1\right) \cdot \left(\frac{y - 16 \cdot m}{2 \cdot m}^{2} + \mathit{gamma}^{2} + 1\right) \cdot \operatorname{exp}\left(\frac{0 - \left(y - 16 \cdot m\right)^{2}}{4 \cdot m}\right)}{\operatorname{sqrt}\left(4 \cdot \operatorname{pi}\left(\right) \cdot m\right)}\right) \cdot \operatorname{exp}\left(z \cdot \operatorname{ofReal}\left(y\right)\right)\right) = \left(\left(16 \cdot m + 2 \cdot m \cdot z + 1\right) \cdot \left(z^{2} + \mathit{gamma}^{2} + 1 + \frac{1}{2 \cdot m}\right) + 2 \cdot z\right) \cdot \operatorname{exp}\left(m \cdot z^{2} + 16 \cdot m \cdot z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/CompleteLowHGaussianMoment.cubic_gaussian_moment_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real m with 0 < m, arbitrary real gamma, and arbitrary complex z, the displayed real density integral equals the displayed complex polynomial times exp(m*z^2 + 16*m*z). The polynomial retains the tilted center 16*m + 2*m*z + 1, the term 1/(2*m), and the explicit +2*z covariance correction. The preceding cubic_gaussian_moment theorem gives the same identity through the named density moments; this Describe records the expanded author statement without introducing a wrapper.

The applicability boundary is exactly m > 0, gamma in the reals, and z in the complexes. No height, strip, finite family, spectral mean, Robin, QGP, or RH premise is added. The Mathlib Gaussian and complex-MGF results are analytic inputs; they are not certificate fields or computational utility.

## References

- Truth anchor: `D5/S3/Arith/Robin/CompleteLowHGaussianMoment.cubic_gaussian_moment_explicit`
