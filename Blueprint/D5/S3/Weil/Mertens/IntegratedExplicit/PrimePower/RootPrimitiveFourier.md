# Frequency extraction for a summable exponential series

## Abstract

Quantitative extraction of a matching frequency family

**Theorem 1.1 (The average recovers the sum over all matching indices).**

$$\forall a \in \mathbb{C}^{\mathbb{N}},\; \forall v \in \mathbb{C}^{\mathbb{N}},\; \forall w \in \mathbb{C},\; \left(\operatorname{SummableNorm}\left(a\right) \land \left(\left(\forall k \in \mathbb{N},\; \operatorname{Re}\left(\operatorname{v}\left(k\right)\right) = 0\right) \land \operatorname{Re}\left(w\right) = 0\right)\right) \Rightarrow \left(\forall d \in \mathbb{R},\; \left(0 < d \land \left(\forall k \in \mathbb{N},\; \operatorname{v}\left(k\right) \ne w \Rightarrow d \le \left\lVert \operatorname{v}\left(k\right) - w \right\rVert\right)\right) \Rightarrow \left(\forall U \in \mathbb{R},\; \forall T \in \mathbb{R},\; 0 < T \Rightarrow \left(\operatorname{Integrable}\left(a, v, w, U, T\right) \land \left\lVert \operatorname{Avg}\left(a, v, w, U, T\right) - \operatorname{B}\left(a, v, w\right) \right\rVert \le \frac{\operatorname{M}\left(a\right) \cdot \frac{2}{d}}{T}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier.spectral_fiber_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write a(k) for the complex coefficients and v(k) for the complex modes. All modes and the tested mode w are purely imaginary. M(a) is the sum of the coefficient norms, and SummableNorm(a) asserts its summability. B(a,v,w) sums a(k) over every k with v(k)=w.

Avg(a,v,w,U,T) is the integral from U to U+T of the series with terms a(k) exp(v(k)u) multiplied by exp(−wu), divided by T. Integrable is Lebesgue interval integrability of the same integrand.

Every matching term is constant after modulation. The nonmatching series has modes v(k)−w at distance at least d from zero. Termwise integration bounds its interval integral by 2M(a)/d independently of U and T.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier.spectral_fiber_average`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum](RootSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowMean](../RHPrimeWindowMean.md)
