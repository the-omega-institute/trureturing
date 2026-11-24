# First contact at the high-threshold boundary

## Abstract

The largest intermediate cosine level determines the high-threshold boundary for every modulus at least thirteen.

For modulus q let c(q,i) = cos(2πi/q), with u(q) = c(q,1), l(q) = c(q,⌊q/2⌋) and v(q) = cos(4π/q). Let a(q) be the exact high-threshold cutoff from the finite three-level certificate, and b(q) the common tail moment. Use r(q) = (1−a(q))/(1−b(q)), the upper tail fraction p(q), and counts N(q), M(q) at u(q), l(q) respectively. The law w(q,i) has weights determined by r(q), p(q) and these counts.

**Theorem 1.1 (The first intermediate contact and the strictly positive multipliers).**

$$\begin{aligned}&\forall q \in \mathbb{N}, 13 \le q \longrightarrow [\\&\operatorname{l}\left(q\right) < \operatorname{v}\left(q\right), \operatorname{v}\left(q\right) < \operatorname{u}\left(q\right), \exists i \in \operatorname{Fin}\left(q\right),\; \operatorname{c}\left(q, i\right) = \operatorname{v}\left(q\right), 0 < \operatorname{r}\left(q\right) \land \operatorname{r}\left(q\right) < 1,\\&0 < \operatorname{B}\left(q\right) \land 0 < \operatorname{G}\left(q\right), \operatorname{P}\left(q, \operatorname{v}\left(q\right)\right) = 0, \forall i \in \operatorname{Fin}\left(q\right),\; \left(\operatorname{l}\left(q\right) < \operatorname{c}\left(q, i\right) \land \left(\operatorname{c}\left(q, i\right) < \operatorname{u}\left(q\right) \land \operatorname{c}\left(q, i\right) \ne \operatorname{v}\left(q\right)\right)\right) \Rightarrow \operatorname{P}\left(q, \operatorname{c}\left(q, i\right)\right) < 0,\\&\operatorname{P}\left(q, 1\right) = 1 - \operatorname{r}\left(q\right) \land \left(\operatorname{P}\left(q, \operatorname{u}\left(q\right)\right) = \frac{\operatorname{r}\left(q\right) \cdot \operatorname{p}\left(q\right)}{\operatorname{N}\left(q\right)} \land \operatorname{P}\left(q, \operatorname{l}\left(q\right)\right) = \frac{\operatorname{r}\left(q\right) \cdot \left(1 - \operatorname{p}\left(q\right)\right)}{\operatorname{M}\left(q\right)}\right),\\&\forall x \in \mathbb{R},\; \operatorname{P}\left(q, x\right) = \operatorname{A}\left(q\right) + \operatorname{B}\left(q\right) \cdot x + \operatorname{G}\left(q\right) \cdot \left(2 \cdot x^{2} - 1\right),\\&\forall i \in \operatorname{Fin}\left(q\right),\; \operatorname{w}\left(q, i\right) = \operatorname{max}\left(0, \operatorname{P}\left(q, \operatorname{c}\left(q, i\right)\right)\right), \operatorname{Certified}\left(q\right),\\&\operatorname{a}\left(q\right) < 1, \operatorname{PAt}\left(q, 1, \operatorname{v}\left(q\right)\right) < 0,\\&\forall s \in \mathbb{R},\; \operatorname{PAt}\left(q, s, \operatorname{v}\left(q\right)\right) = \operatorname{PAt}\left(q, 1, \operatorname{v}\left(q\right)\right) \cdot \frac{s - \operatorname{a}\left(q\right)}{1 - \operatorname{a}\left(q\right)}]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_threshold_first_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P(q,x) denotes the quadratic interpolant at the cutoff and A(q), B(q), G(q) are its coefficients in the basis 1, x, 2x²−1. With Lagrange coefficients T, U, L at the three nodes, A(q) = T u(q) l(q) + U l(q) + L u(q) + G(q). Certified(q) is the finite certificate at a(q), including normalized nonnegative weights, both moments equal to a(q), the exact squared mass, the squared-distance bound for every feasible competitor and uniqueness. At a general real threshold s, PAt(q,s,x) uses tail mass (1−s)/(1−b(q)). The affine crossing gives a negative value at v(q) above the cutoff and a positive value below it.

The slope for an intermediate level is the quadratic-multiplier slope plus nonnegative multiples of the reciprocals of its two distances from the outer cosine levels. The upper per-residue share p(q)/N(q) per unit of tail mass tends to one half, and the lower share (1−p(q))/M(q) tends to zero. For even moduli the lowest intermediate level is −u(q) and u(q)>8/9. For odd moduli the lower gap is at least 2 cos(π/q)(1−u(q)). These comparisons give strict dominance at v(q) from modulus thirteen.

**Theorem 1.2 (Sharpness at modulus twelve).**

$$\operatorname{P}\left(12, \operatorname{v}\left(12\right)\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_threshold_twelve_no_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At modulus twelve the interval starts with a negative interpolant at v(12). The lowest intermediate level is −u, attained at residue five. Here u=√3/2, the lower level is −1 with multiplicity one, and g(u)(2u+1)=1 for g(x)=(1−x)(2x+1). The slope at −u is strictly greater than the slope at v(12), so v(12) has not reached zero at the exact cutoff.

**Theorem 1.3 (The sharp asymptotic width of the high-threshold interval).**

$$\operatorname{TendstoAtTop}\left((q:\mathbb{N}\mapsto q^{2} \cdot \left(1 - \operatorname{a}\left(q\right)\right)), \frac{24 \cdot \pi^{2}}{5}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_criticalThreshold_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As q tends to infinity, the winning slope tends to 5/3. After division by 1−u(q), the tail-moment deficit tends to 4. The half-angle identity and the sine quotient limit give q²(1−u(q)) tending to 2π². Together these determine the limit.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_criticalThreshold_limit`
- Truth anchor: `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_threshold_first_contact`
- Truth anchor: `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_threshold_twelve_no_contact`
- Dependency: [D5/S3/Fourier/Concentration/HighCosineThreshold](../Concentration/HighCosineThreshold.md)
