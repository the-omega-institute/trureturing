# Agreement of Low-Degree Collision Masses

## Abstract

Two spectra agree at every degree below a prescribed threshold and differ at growing degree.

For a natural number k≥2, take the triples (0,1,k) and (0,1,k+√2) with weights (1/4,1/4,1/2). Let E(p,t) and F(p,t) be their respective weighted ordered-pair collision masses for degree p and closed gap bound t. In the display, the first line holds at every natural degree p<k, and the first two lines hold for every real t with 0≤t<1. The last two inequalities hold for every natural p>0 with t_p=1/(2(k+3)p).

**Theorem 1.1 (Coincident low-degree masses allow different high-degree rates).**

$$\begin{aligned}\operatorname{E}\left(p, t\right) = \operatorname{F}\left(p, t\right)\\\operatorname{E}\left(k, t\right) = \operatorname{F}\left(k, t\right) + 2 \cdot k \cdot {\frac{1}{4}}^{k-1} \cdot {\frac{1}{4}}^{k} \cdot \frac{1}{2}\\\frac{1}{16 \cdot k \cdot \sqrt{p}} \leq \operatorname{E}\left(p, t_{p}\right)\\\operatorname{F}\left(p, t_{p}\right) \leq \frac{4}{p}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/LowOrderCollisionAgreement.low_order_agreement_and_high_order_disparity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Below degree k, differing counts on the last coordinate force a gap of at least one in both spectra. At degree k the integer spectrum gains the two ordered pairs between (0,k,0) and (k−1,0,1).

At growing degree the integer spectrum keeps the mass lower bound from its variance. For the irrational spectrum, a nonzero integer quadratic norm separates all distinct degree vectors at t_p. On the remaining diagonal, the multinomial weights factor into two fair binomial weights. A central binomial bound and monotonicity in the upper tail bound their product. These are comparison spectra for testing what low-degree collision measurements determine.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/LowOrderCollisionAgreement.low_order_agreement_and_high_order_disparity`
- Dependency: [D5/S3/Fourier/Concentration/FiniteCollisionVariance](FiniteCollisionVariance.md)
