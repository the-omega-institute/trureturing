# Real-frequency collision variance bound

## Abstract

A positive angular Fejer kernel retains a closed collision band for arbitrary real frequency sums.

Fix a finite index set J, real frequencies g(j), real weights w(j), and a positive resolution eta. Let S(t)=sum_j w(j) exp(i g(j)t), W=sum_j w(j). For natural degree p, the index family consists of the nonnegative integer multiplicity vectors of total degree p. Write G(m) for their frequency sums and c(m) for their multinomial weights. E(p) is the sum of c(m)c(n) over the ordered pairs with |G(m)-G(n)|<=eta. Set K(t)=eta/(2 pi) sinc(eta t/2)^2 and phi(d)=max(0,1-|d|/eta). Write M(p) for the whole-line integral of K(t)|S(t)|^(2p) and T(p) for the finite double sum of c(m)c(n)phi(G(m)-G(n)).

**Theorem 1.1 (Exact triangular-band comparison).**

$$\operatorname{M}\left(p\right) = \operatorname{T}\left(p\right) \land \left(\operatorname{Nonnegative}\left(w\right) \Rightarrow \operatorname{M}\left(p\right) \le \operatorname{E}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FejerCollisionVariance.fejer_collision_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all signed weights the exact finite pair expansion of the even score power and integration of each cosine against K give M(p)=T(p). The existing angular Fejer law supplies the integrability, nonnegativity and exact triangular Fourier transform. If the input weights are nonnegative, every multinomial pair weight is nonnegative, and phi(d) is bounded by the indicator of |d|<=eta. The comparison includes the closed band boundary, where phi is zero.

**Theorem 1.2 (Retained finite-window contribution).**

$$W^{2 \cdot p} \cdot \operatorname{I}\left(p, A\right) \le \operatorname{E}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FejerCollisionVariance.fejer_collision_variance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative weights assume sum_j w(j)(g(j)-a)^2<=V W around an arbitrary real center a and with real budget V. For each A>=0 let I(p,A) denote the integral of K(t) max(0,1-Vt^2/2)^(2p) from -A to A. The pointwise score variance minorant gives the claimed bound inside the window. The positive kernel allows this integral to be bounded by the full-line weighted score moment, which is already controlled by E(p). There is no lattice restriction on the frequencies.

**Theorem 1.3 (Gaussian lower coefficient at fixed positive resolution).**

$$\forall \varepsilon > 0, \operatorname{Eventually}\left(\left(\frac{eta}{2 \cdot \sqrt{\pi}} - \varepsilon\right) \cdot W^{2 \cdot p} \le \sqrt{p \cdot V} \cdot \operatorname{E}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FejerCollisionVariance.fejer_collision_asymptotic_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In addition assume V>0 and keep all data, V and eta fixed while p tends to infinity. For each epsilon>0, put c=eta/(2 pi)-epsilon/(2 sqrt(pi)). Since K(0)=eta/(2 pi) and K is continuous, there is a fixed positive A such that K(t)>=c for |t|<=A. The scaled unweighted clipped power integral on this window tends to sqrt(pi). Consequently its product with c tends to eta/(2 sqrt(pi))-epsilon/2. For all sufficiently large p it exceeds the required coefficient. Apply the finite-window bound with the same variance and weights. The result is a lower bound for arbitrary real frequency families, including finite zeta tails. Uniformity for growing families or changing eta and V, and upper bounds for actual high-degree collisions, require further estimates.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FejerCollisionVariance.fejer_collision_asymptotic_lower`
- Truth anchor: `D5/S3/Fourier/Concentration/FejerCollisionVariance.fejer_collision_comparison`
- Truth anchor: `D5/S3/Fourier/Concentration/FejerCollisionVariance.fejer_collision_variance_lower`
- Dependency: [D5/S3/Analytic/Fourier/AngularFejerKernel](../../Analytic/Fourier/AngularFejerKernel.md)
- Dependency: [D5/S3/Fourier/Asymptotics/ClippedGaussianMinorant](../Asymptotics/ClippedGaussianMinorant.md)
- Dependency: [D5/S3/Fourier/Concentration/LatticeConvolutionVariance](LatticeConvolutionVariance.md)
