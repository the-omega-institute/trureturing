# First-order rear activation

## Abstract

A first-order expansion selects the adjacent rear support even at a leading activation threshold.

Fix a nonempty finite rear offset set S and mesh sequence h. Write Q_n=3n⁵h(n)²/20, suppose n⁵h(n)²→K, Q=3K/20, and n(Q_n−Q)→L. For a real offset r, define D=|S|r²−∑_{s∈S}s². The signed rear value p_n(r) uses the coupled three-moment fit.

**Theorem 1.1 (Quadratically amplified moment and point errors).**

$$\operatorname{Limit}\left(n^{2} \cdot \operatorname{MomentError}\left(n\right)\right) = 0 \land \operatorname{Limit}\left(n^{2} \cdot \operatorname{PointError}\left(n, r\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder.second_order_remainders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a convergent finite critical scale n⁵h(n)², the exact bottom moment target minus C_n∑_{s∈S}s²+|S|B_n vanishes after multiplication by n². At any fixed real offset r the error n³p_n(r)−(C_n r²+B_n) also vanishes after multiplication by n². Uniform front bounds and the quadratic trigonometric remainder on each fixed rear offset give both limits.

**Theorem 1.2 (First-order signed rear value).**

$$\operatorname{Limit}\left(n \cdot \left(\operatorname{Card}\left(S\right) \cdot n^{3} \cdot \operatorname{RearValue}\left(n, r\right) - \left(Q - \frac{3}{4} \cdot D\right)\right)\right) = L + Q + \frac{9}{8} \cdot D$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder.scaled_rear_first_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact lattice normalizer is (4/3)n³+2n²−n/3−1/2. The refined front-coefficient estimate transfers n(C_n+3/4)→9/8 to the coupled fit. The bottom moment row differs from (0,∑_{s∈S}s²,|S|) by o(1/n). Uniform bounds on the growing front and pointwise bounds on the finite rear set prove this rate. The point readout differs from C_n r²+B_n by o(1/n) after scaling by n³. Eliminating B_n using the exact bottom target Q_n(1+1/n) gives the displayed limit.

**Theorem 1.3 (Support at leading threshold equality).**

$$\left(0 < L + \frac{5}{2} \cdot Q \Rightarrow k = l + 1\right) \land \left(L + \frac{5}{2} \cdot Q < 0 \Rightarrow k = l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder.eventual_support_at_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q(n)>0 be integral, h(n)=2π/q(n), and let e be the eventual parity. Fix l≥0 with Q=T_e(l+1). If L+5Q/2 is nonzero, the adjacent support index is l+1 when this quantity is positive and l otherwise.

The two adjacent candidate windows have the same zero-boundary threshold identity. The first-order limit controls the sign at that level. The other rear boundary and both front boundaries have strict leading signs, so the full finite optimizer certificate applies. The fitted law is feasible, both cosine moments equal 1−2n(n+1)h²/5, and energy exceeds its minimum by at least the squared distance to the fitted law. Its exact positive support is the front and selected rear window. The further degeneracy L+5Q/2=0 is excluded.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder.eventual_support_at_threshold`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder.scaled_rear_first_order`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder.second_order_remainders`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicGrowingSupport](CyclicGrowingSupport.md)
