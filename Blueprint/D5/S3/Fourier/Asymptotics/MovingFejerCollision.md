# Uniform collision lower bound at moving resolution

## Abstract

A compatible variance and resolution window yields a collision lower bound with a threshold independent of the frequency family.

Let V(n) and eta(n) be real sequences indexed by natural n, both eventually positive. Write s(n)=sqrt(n V(n)) and r(n)=eta(n)/s(n).

**Theorem 1.1 (Compatibility of the two window scales).**

$$\lim_{n \to \infty} \operatorname{r}\left(n\right) = 0 \Leftrightarrow \left(\exists A \in \mathbb{R}^{\mathbb{N}},\; \operatorname{EventuallyPositive}\left(A\right) \land \left(\lim_{n \to \infty} \operatorname{A}\left(n\right) \cdot \operatorname{s}\left(n\right) = \infty \land \lim_{n \to \infty} \operatorname{eta}\left(n\right) \cdot \operatorname{A}\left(n\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/MovingFejerCollision.exists_fejer_window_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If r(n) tends to zero, choose A(n)=1/(s(n)sqrt(r(n))). Eventually all factors are positive. The normalized radius A(n)s(n) equals 1/sqrt(r(n)) and tends to positive infinity. The resolution-scaled radius eta(n)A(n) equals sqrt(r(n)) and tends to zero. Conversely, for any such eventually positive A(n), r(n)=(eta(n)A(n))/(s(n)A(n)) eventually, whose limit is zero.

**Theorem 1.2 (Uniform Gaussian lower coefficient).**

$$\forall \varepsilon > 0, \operatorname{EventuallyForAllData}\left(\left(\frac{1}{2 \cdot \sqrt{\pi}} - \varepsilon\right) \cdot \operatorname{eta}\left(n\right) \cdot W^{2 \cdot n} \le \operatorname{s}\left(n\right) \cdot \operatorname{E}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/MovingFejerCollision.moving_fejer_uniform_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume r(n) tends to zero. For each epsilon>0, the degree threshold comes before the choice of finite index type J, real frequencies g(j), nonnegative weights w(j), or real center a. Let W be the sum of the weights, E(n) the ordered-pair collision mass of degree-n frequency sums at the closed resolution eta(n), and assume sum_j w(j)(g(j)-a)^2 <= V(n) W. All such data beyond the threshold satisfy the bound.

Take the compatible window A(n) and set c=1/(2 pi)-epsilon/(2 sqrt(pi)). The normalized angular Fejer kernel equals (1/(2 pi)) sinc(eta(n)t/2)^2. It is at least c throughout the window eventually, since eta(n)A(n) tends to zero and sinc is continuous at zero. The scaled unweighted clipped integral over this window tends to sqrt(pi) because A(n)s(n) tends to infinity. Thus its product with c tends to 1/(2 sqrt(pi))-epsilon/2. Apply the finite-window collision inequality with the same n and budget. This argument gives a threshold depending only on the two sequences and epsilon, allowing the frequency family and its cardinality to vary.

For example, with positive total weight the bound yields a liminf of at least 1/(2 sqrt(pi)) for s(n)E(n)/(eta(n)W^(2n)). The small-resolution hypothesis is essential to this argument: even a single unit-weight frequency with V(n)=1/n² and fixed positive eta has scaled collision ratio tending to zero. Uniform upper bounds for high-degree collisions of actual zeta ordinates remain open.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/MovingFejerCollision.exists_fejer_window_iff`
- Truth anchor: `D5/S3/Fourier/Asymptotics/MovingFejerCollision.moving_fejer_uniform_lower`
- Dependency: [D5/S3/Fourier/Concentration/FejerCollisionVariance](../Concentration/FejerCollisionVariance.md)
