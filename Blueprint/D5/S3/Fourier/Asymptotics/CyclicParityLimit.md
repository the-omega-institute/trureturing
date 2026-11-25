# Parity correction for the cyclic minimum

## Abstract

The scaled difference between the lattice and cyclic minima has an exact limit on each parity.

**Theorem 1.1 (The gap on the even and odd moduli).**

$$\lim_{k \to \infty} (\operatorname{q}\left(k\right)^{2} \cdot \left(\operatorname{L}\left(m\right) - \operatorname{CyclicMinimum}\left(\operatorname{q}\left(k\right), 1 - \frac{\lambda}{\operatorname{q}\left(k\right)^{2}}\right)\right)) = \frac{2}{Z} \cdot \left(\left(t - d^{2}\right) \cdot \frac{3 \cdot \lambda}{8} + \frac{4 \cdot \pi^{2}}{3} \cdot m_{4}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicParityLimit.cyclic_parity_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any positive budget λ and put m=λ/(8π²). The activation data have positive index n with (n²−1)/5≤m<n(n+2)/5. The normalized law is w(j)=(t−j²)₊/Z. Its squared mass is L(m) and its fourth moment is m₄=Σ j⁴w(j).

Write q=2k+2 on the even sequence, where d=0, and q=2k+1 on the odd sequence, where d=1/2. The feasible weights have first and second cosine moments at least 1−λ/q². On each sequence a minimizer exists for all sufficiently large k. The displayed limit means that for each positive tolerance all minimizers satisfy it within that tolerance for all sufficiently large k.

Set h=2π/q. The quadratic vanishes at C=−cos(dh). Its other root confines its positive part to a fixed front window for large q. The sixth-order cosine remainder gives the fourth-order deficit expansion on this window and the order-h² change of the quadratic. At a zero of the lattice weight the perturbed squared positive part is bounded by a constant times h⁴.

The moment equations give transfers δ and μ of order h² with μ/h² tending to 3m/4. The center and its nearest neighbors have strictly positive lattice weights for every positive budget. The adjusted probabilities are therefore eventually feasible and saturate both moments. At every site carrying mass the quadratic is nonnegative. The energy exceeds the dual bound by the sum of squared distances to the clipped quadratic, which is bounded by a constant times h⁴. This also gives the limit at each activation threshold.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicParityLimit.cyclic_parity_correction`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicParityCorrection](CyclicParityCorrection.md)
