# Boundary limits in the growing cyclic moment fit

## Abstract

Critical-scale coefficients and signed boundary values for growing cyclic windows.

Fix a nonempty finite set S of real rear offsets and let n tend to infinity. Assume n⁵h(n)² tends to a finite real K. Put m=n(n+1)/5 and prescribe the three scaled moments (1−mh²,m/n²,3n³mh²/4). The coefficient vector a(n) is the inverse of the coupled moment matrix applied to this target.

**Theorem 1.1 (The three fitted coefficients converge).**

$$\operatorname{Limit}\left(\operatorname{Apply}\left(a, n\right)\right) = \operatorname{VectorThree}\left(\frac{3}{4}, 0 - \frac{3}{4}, B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits.coefficient_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The moment target converges to (1,1/5,3K/20). Inverting the limiting coupled matrix gives (3/4,−3/4,B), where B=(3K/20+(3/4)∑_{r∈S}r²)/|S|.

**Theorem 1.2 (The front coefficient error vanishes after multiplication by n).**

$$\operatorname{Limit}\left(n \cdot \left(\operatorname{FrontCoefficients}\left(n\right) - \operatorname{LatticeCoefficients}\left(n\right)\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits.refined_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact lattice reference has radius parameter t=n(n+1)−1/2 and normalizer Z. Its first two coefficients are nt/Z and −n³/Z. After multiplying by n, the top two rows of the coupled matrix minus the lattice Gram rows with a zero third column converge to zero. The target mass perturbation also vanishes under this scaling. Holding the rear coefficient fixed, inversion of the first two rows transfers the scaled residual bound to the two coefficient errors.

**Theorem 1.3 (Signed value at the growing front boundary).**

$$\operatorname{Limit}\left(n^{2} \cdot \operatorname{FrontValue}\left(n, delta\right)\right) = \frac{3}{4} \cdot \left(1 - 2 \cdot delta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits.scaled_boundary_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At x=(n+δ)/n the finite signed weight is the dot product of the coefficient row with a(n). Multiplying by n² gives the limit (3/4)(1−2δ). This gives strictly positive and strictly negative limiting values at δ=0 and δ=1 respectively. The scaled site-feature remainders vanish, including at a fixed offset beyond the fitted window.

**Theorem 1.4 (Signed value at a fixed rear offset).**

$$\operatorname{Limit}\left(n^{3} \cdot \operatorname{RearValue}\left(n, r\right)\right) = B - \frac{3}{4} \cdot r^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits.scaled_rear_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every fixed real rear offset r the signed value multiplied by n³ converges to B−3r²/4. Strict limiting inequalities settle the eventual sign. Zero limiting values require finer estimates. These readouts concern a signed moment fit on the stated windows. Certification of the full cyclic optimizer also requires the cyclic grid correspondence and complement signs.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits.coefficient_tendsto`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits.refined_coefficients`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits.scaled_boundary_value`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits.scaled_rear_value`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicGrowingCoupledFit](CyclicGrowingCoupledFit.md)
