# Finite Tail Moments from Weighted Near-Collisions

## Abstract

Weighted near-collisions control finite-time moments and bound the start of a missing window.

For a finite index type J, write Z(t) for the weighted sum of exp(i g(j)t). A degree-p count vector m has frequency G(m) equal to the sum of m(j)g(j), and coefficient c(m) equal to the multinomial coefficient times the product of w(j) to the power m(j). E(p,r) is the ordered sum of c(m)c(n) over degree-p pairs with absolute frequency difference at most r. M(p,L,s) averages the 2p-th power of the norm of Z(s+u+t) over two independent uniform offsets u and t in the closed interval from -L/2 to L/2.

**Theorem 1.1 (The averaging radius determines the near-collision scale).**

$$\begin{aligned}\forall J: \operatorname{FiniteType},\quad g,w: J\to\mathbb{R},\quad p: \mathbb{N},\\L,s: \mathbb{R},\\(\forall j \in J, \operatorname{w}\left(j\right)\ge0)\quad \land L>0\quad \longrightarrow\\\operatorname{E}\left(p, \frac{2}{L}\right) \cdot \operatorname{sin}\left(1\right)^{2}\le\operatorname{M}\left(p, L, 0\right)\quad \land\\\operatorname{M}\left(p, L, s\right)\le\operatorname{M}\left(p, L, 0\right)\quad \land\quad \operatorname{M}\left(p, L, 0\right)\le(3 + \frac{\pi^{2}}{3}) \cdot \operatorname{E}\left(p, \frac{2}{L}\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.tail_moment_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The power expansion reduces the moment to an ordered pair sum. Each pair contributes a squared sinc at its scaled frequency difference. The cosine factor is at most one, so the moment is maximal at center zero. At that center concavity of sine on [0,1] gives a squared factor of at least sin²(1) for pairs within distance 2/L. For the upper bound, group frequencies into bins of width 2/L. The reciprocal-square majorant has full row sum 3 + π²/3. The shared bin energy estimate bounds the quadratic form by this constant times the sum of squared bin masses. Each same-bin pair lies within the collision radius, including coincident frequencies.

**Theorem 1.2 (The near-collision budget confines the window start).**

$$\begin{aligned}\forall J: \operatorname{FiniteType},\quad g,w: J\to\mathbb{R},\quad p: \mathbb{N},\\L,H,h,\delta,A: \mathbb{R},\\(\forall j \in J, \operatorname{w}\left(j\right)\ge0)\quad \land L>0\quad \land h>0\quad \land \delta\ge0\quad \land\\(3 + \frac{\pi^{2}}{3}) \cdot (\left\lfloor\frac{H}{h}\right\rfloor_{+} + 1) \cdot \operatorname{E}\left(p, \frac{2}{L}\right)<\delta^{2 \cdot p}\quad \longrightarrow\\\exists b: \mathbb{R}, A<b<A + 2 \cdot L\quad \land \forall t \in [b,b + H],\\\left|\sum_{j \in J} \operatorname{w}\left(j\right) \cdot \operatorname{sin}\left(\operatorname{g}\left(j\right) \cdot t\right)\right|<\delta + h \cdot (\sum_{j \in J} \operatorname{w}\left(j\right) \cdot \left|\operatorname{g}\left(j\right)\right|)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.exists_bounded_tail_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Average the sum of the grid moments over candidate starts centered at A+L. The weighted bound is uniform in the center, including every grid offset. If each start in the open interval had a bad grid node, the averaged sum would be at least the power of the threshold. The strict budget therefore gives a common good start in that interval. The complex modulus bounds the absolute imaginary part at grid nodes. The mesh amends it by at most hB throughout the closed window, including its right endpoint.

This result gives a finite search interval when an estimate of the weighted collision mass is supplied at the corresponding resolution. It applies to repeated frequencies. For a tail of actual zeta ordinates at moment order growing with the cutoff, the necessary arithmetic estimate remains open.

`D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow`

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.exists_bounded_tail_window`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.tail_moment_comparison`
- Dependency: [D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow](FiniteTailMomentMissingWindow.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/SpectralSampling](../../Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/SpectralSampling.md)
- Narrative reference: [D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow](FiniteTailMomentMissingWindow.md)
