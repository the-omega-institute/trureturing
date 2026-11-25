# Displacement of a cyclic activation threshold

## Abstract

The front support changes at one parity-dependent budget near each positive lattice activation.

**Theorem 1.1 (The switch, its coefficient, and the support on both sides).**

$$\exists eps \in Real,\; \exists r \in \operatorname{RealSequences}\left(\right),\; 0 < eps \land \left(\operatorname{Limit}\left(\frac{\operatorname{r}\left(k\right) - m_{0}}{h^{2}}\right) = \frac{\left(n^{2} - 1\right) \cdot \left(63 \cdot d^{2} + 47 - 31 \cdot n^{2}\right)}{420} \land \operatorname{EventuallyAtTop}\left(k, \left(m_{0} - eps < \operatorname{r}\left(k\right) \land \operatorname{r}\left(k\right) < m_{0} + eps\right) \land \left(\forall m \in \operatorname{ClosedInterval}\left(m_{0} - eps, m_{0} + eps\right),\; \exists v \in \operatorname{Feasible}\left(q, 1 - 2 \cdot m \cdot h^{2}\right),\; \left(\operatorname{M}\left(1, v\right) = 1 - 2 \cdot m \cdot h^{2} \land \operatorname{M}\left(2, v\right) = 1 - 2 \cdot m \cdot h^{2}\right) \land \left(\left(\forall w \in \operatorname{Feasible}\left(q, 1 - 2 \cdot m \cdot h^{2}\right),\; w \ne v \Rightarrow \operatorname{E}\left(v\right) < \operatorname{E}\left(w\right)\right) \land \left(\forall i \in \operatorname{ZMod}\left(q\right),\; 0 < \operatorname{PositivePart}\left(\operatorname{v}\left(i\right)\right) \Leftrightarrow \left(\operatorname{Abs}\left(\operatorname{Centered}\left(i\right)\right) < n \lor \left(\left(\operatorname{r}\left(k\right) < m \land \operatorname{Abs}\left(\operatorname{Centered}\left(i\right)\right) = n\right) \lor \operatorname{c}\left(i\right) = \operatorname{AntipodalCosine}\left(q\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicActivationShift.cyclic_activation_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an integer n≥2 and a parity. The moduli q are 2k+2 in the even case and 2k+1 in the odd case. Write h=2π/q and m₀=(n²−1)/5, and take d=0 or d=1/2 respectively. There are a fixed ε>0 and switch budgets r(k) whose shift in units h² has the displayed limit as k tends to infinity.

For all sufficiently large k, the budget r(k) belongs to (m₀−ε,m₀+ε). For every m in the closed ε-neighborhood of m₀, with moment floor θ=1−2mh², there is a feasible law v attaining both floors. Its squared mass is strictly smaller than that of every other feasible law. The support display uses the absolute value of the centered representative j and c_min, the sampled first cosine at floor(q/2). The boundary pair ±n enters only when m exceeds r(k).

On the inclusive front window and nearest antipodal sites, the moment solve is affine in m. The boundary reading has positive limiting slope. The shift is the negative ratio of its mesh-squared variation to that slope. The front fourth moment equals (n²−1)(3n²−5)/35. The total antipodal variation equals 3m₀/4 and its squared offset is d².

At the switch the vanishing boundary readings allow the same fit on both windows. The bounding excluded cosine levels have strict negative signs, which extend by convexity to the complement of the inclusive window and closest antipodal sites. Interpolating the switch certificate with fixed certified budgets on the two sides gives the optimizer throughout the neighborhood.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicActivationShift.cyclic_activation_shift`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicEventualSupport](CyclicEventualSupport.md)
