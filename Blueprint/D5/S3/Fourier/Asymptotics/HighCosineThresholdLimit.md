# First contact at the high-threshold boundary

## Abstract

The largest intermediate cosine level determines the high-threshold boundary for large cycles.

For modulus q let c(q,i) = cos(2πi/q), with u(q) = c(q,1), l(q) = c(q,⌊q/2⌋) and v(q) = cos(4π/q). Let a(q) be the exact high-threshold cutoff from the finite three-level certificate, and b(q) the common tail moment. Use r(q) = (1−a(q))/(1−b(q)), the upper tail fraction p(q), and counts N(q), M(q) at u(q), l(q) respectively. The law w(q,i) has weights determined by r(q), p(q) and these counts.

**Theorem 1.1 (The first intermediate contact and the strictly positive multipliers).**

$$\begin{aligned}&\exists Q \in \mathbb{N}, \forall q \in \mathbb{N}, Q \le q \longrightarrow [\\&\operatorname{l}\left(q\right) < \operatorname{v}\left(q\right), \operatorname{v}\left(q\right) < \operatorname{u}\left(q\right), \exists i \in \operatorname{Fin}\left(q\right),\; \operatorname{c}\left(q, i\right) = \operatorname{v}\left(q\right), 0 < \operatorname{r}\left(q\right) \land \operatorname{r}\left(q\right) < 1,\\&0 < \operatorname{B}\left(q\right) \land 0 < \operatorname{G}\left(q\right), \operatorname{P}\left(q, \operatorname{v}\left(q\right)\right) = 0, \forall i \in \operatorname{Fin}\left(q\right),\; \left(\operatorname{l}\left(q\right) < \operatorname{c}\left(q, i\right) \land \left(\operatorname{c}\left(q, i\right) < \operatorname{u}\left(q\right) \land \operatorname{c}\left(q, i\right) \ne \operatorname{v}\left(q\right)\right)\right) \Rightarrow \operatorname{P}\left(q, \operatorname{c}\left(q, i\right)\right) < 0,\\&\operatorname{P}\left(q, 1\right) = 1 - \operatorname{r}\left(q\right) \land \left(\operatorname{P}\left(q, \operatorname{u}\left(q\right)\right) = \frac{\operatorname{r}\left(q\right) \cdot \operatorname{p}\left(q\right)}{\operatorname{N}\left(q\right)} \land \operatorname{P}\left(q, \operatorname{l}\left(q\right)\right) = \frac{\operatorname{r}\left(q\right) \cdot \left(1 - \operatorname{p}\left(q\right)\right)}{\operatorname{M}\left(q\right)}\right),\\&\forall x \in \mathbb{R},\; \operatorname{P}\left(q, x\right) = \operatorname{A}\left(q\right) + \operatorname{B}\left(q\right) \cdot x + \operatorname{G}\left(q\right) \cdot \left(2 \cdot x^{2} - 1\right),\\&\forall i \in \operatorname{Fin}\left(q\right),\; \operatorname{w}\left(q, i\right) = \operatorname{max}\left(0, \operatorname{P}\left(q, \operatorname{c}\left(q, i\right)\right)\right), \operatorname{Certified}\left(q\right)]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_threshold_first_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P(q,x) denotes the quadratic interpolant at the cutoff and A(q), B(q), G(q) are its coefficients in the basis 1, x, 2x²−1. With Lagrange coefficients T, U, L at the three nodes, A(q) = T u(q) l(q) + U l(q) + L u(q) + G(q). Certified(q) is the finite certificate at a(q), including normalized nonnegative weights, both moments equal to a(q), the exact squared mass, the squared-distance bound for every feasible competitor and uniqueness.

The slope for an intermediate level is the quadratic-multiplier slope plus nonnegative multiples of the reciprocals of its two distances from the outer cosine levels. The lower distance is at least 1−u(q) for either parity. The upper per-residue mass tends to one half and the lower per-residue mass tends to zero. The two reciprocal terms then give a strict comparison in favor of v(q), uniform over all the other intermediate levels.

**Theorem 1.2 (The sharp asymptotic width of the high-threshold interval).**

$$\operatorname{TendstoAtTop}\left((q:\mathbb{N}\mapsto q^{2} \cdot \left(1 - \operatorname{a}\left(q\right)\right)), \frac{24 \cdot \pi^{2}}{5}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_criticalThreshold_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As q tends to infinity, the winning slope tends to 5/3. After division by 1−u(q), the tail-moment deficit tends to 4. The half-angle identity and the sine quotient limit give q²(1−u(q)) tending to 2π². Together these determine the limit.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_criticalThreshold_limit`
- Truth anchor: `D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit.cyclic_threshold_first_contact`
- Dependency: [D5/S3/Fourier/Concentration/HighCosineThreshold](../Concentration/HighCosineThreshold.md)
