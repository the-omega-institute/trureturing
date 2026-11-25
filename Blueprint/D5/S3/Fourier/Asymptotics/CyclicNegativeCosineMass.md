# Negative-cosine mass of joint cyclic minimizers

## Abstract

The first-moment deficit determines the rescaled mass near the antipode.

**Theorem 1.1 (Mass and localization on the negative-cosine half of the cycle).**

$$\operatorname{TendstoAtTop}\left(\operatorname{Mass}\left(q\right), \frac{3 \cdot \lambda}{8}\right), \operatorname{TendstoAtTop}\left(\operatorname{Error}\left(q\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicNegativeCosineMass.cyclic_negative_cosine_mass_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix λ≥0. For every sufficiently large positive integer q let v_q be a global least-squared-mass probability on the full cycle whose first and second cosine moments are both at least 1−λ/q². No choice of optimizer is fixed. Let A(q) be the residues i with c(q,i)=cos(2πi/q)<0. Write Mass(q) for q² times the sum of v_q over A(q), and Error(q) for the same rescaled sum with each weight multiplied by 1+c(q,i). Both limits take all positive moduli.

The cyclic-to-lattice comparison gives convergence at each fixed lattice site. The half-angle formula gives the scaled cosine deficit limits on those sites. The lattice second moment, multiplied by 8π², equals λ. The finite optimizers have both scaled deficits equal to λ, so the contribution to the second deficit outside the fixed support tends to zero. At λ=0, both moment equalities follow from feasibility and the pointwise cosine upper bound one.

Where c≥0 the first deficit 1−c is bounded by half the second deficit. Where c<0, the same bound holds for 1+c. The scaled first deficit over the nonnegative-cosine half therefore tends to λ/4, its limit on the fixed lattice sites. The remaining first deficit plus Error(q) equals twice Mass(q), which gives the coefficient 3/8.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicNegativeCosineMass.cyclic_negative_cosine_mass_limit`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicToLatticeComparison](CyclicToLatticeComparison.md)
- Dependency: [D5/S3/Fourier/Concentration/ActiveCosineConstraints](../Concentration/ActiveCosineConstraints.md)
