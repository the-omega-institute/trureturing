# Second-order rear activation

## Abstract

A quadratic correction resolves the zero first-order rear activation margin.

Fix a nonempty finite rear offset set S and mesh sequence h. Define Q_n=3n⁵h(n)²/20. Assume Q_n→Q=3K/20, n(Q_n−Q)→L and n(n(Q_n−Q)−L)→H. For an offset r, set D=|S|r²−∑_{s∈S}s² and denote the signed rear weight by p_n(r).

**Theorem 1.1 (Second-order signed rear value).**

$$\operatorname{Limit}\left(n \cdot \left(n \cdot \left(\operatorname{Card}\left(S\right) \cdot n^{3} \cdot \operatorname{RearValue}\left(n, r\right) - \left(Q - \frac{3}{4} \cdot D\right)\right) - \left(L + Q + \frac{9}{8} \cdot D\right)\right)\right) = H + L - \frac{15}{8} \cdot D$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingRearSecondOrder.scaled_rear_second_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact normalizer yields n(n(C_lat+3/4)−9/8)→−15/8, and the cubic coefficient-error bound transfers this to C_n. The uniform front contribution and finite rear feature errors vanish after quadratic amplification. Therefore the amplified bottom-row and point-readout errors also vanish at that scale. Eliminate B_n using the exact target Q_n(1+1/n) to obtain the second-order limit.

**Theorem 1.2 (Support when the first-order margin vanishes).**

$$\left(0 < H - 5 \cdot Q \Rightarrow k = l + 1\right) \land \left(H - 5 \cdot Q < 0 \Rightarrow k = l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingRearSecondOrder.eventual_support_at_second_order_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose q(n)>0 are integer periods of eventual parity e, h(n)=2π/q(n), Q=T_e(l+1), and L+5Q/2=0. The disputed outer level has 3D/4=Q for both adjacent windows. The quadratic correction is H−5Q. If this is nonzero, the selected index k is l+1 for positive correction and l for negative correction.

The other endpoint signs are strict at the leading scale. The finite certificate gives feasibility, both exact cosine moment floors, uniqueness and the squared-distance energy inequality. The positive support consists of the front window and the selected rear window. The further degeneracy H=5Q is excluded.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingRearSecondOrder.eventual_support_at_second_order_threshold`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingRearSecondOrder.scaled_rear_second_order`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder](CyclicGrowingRearFirstOrder.md)
