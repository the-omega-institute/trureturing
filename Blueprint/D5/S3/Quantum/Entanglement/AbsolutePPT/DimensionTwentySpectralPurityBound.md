# Sharp length-twenty spectral purity

## Abstract

The rank-three length-twenty spectral relaxation has greatest purity 7/121.

**Theorem 1.1 (Universal spectral inequality).**

$$\forall (l:Fin\left(20\right)\to \mathbb{R}),(((Antitone\left(l\right))\land (\forall (i:Fin\left(11 + 9\right)),(0\leq l\left(i\right)))\land (\sum_{i:Fin\left(11 + 9\right)}(l\left(i\right))=1)\land (PosSemidef\left(K1\left(boundaryValues\left(11, l\right)\right)\right))\land (PosSemidef\left(K2\left(boundaryValues\left(11, l\right)\right)\right)))\Rightarrow (\sum_{i:Fin\left(20\right)}((l\left(i\right))^{2})\leq \frac{7}{121}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound.spectral_purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every antitone nonnegative real spectrum on Fin 20 with mass one and both rank-three boundary matrices positive semidefinite, the square sum is at most 7/121. The existing N6 and N7 rational certificate bounds give the endpoints at lengths 18 and 21. SpectralBoundaryTransfer first gives length 19 using a=2, then length 20 using a=1. Length 19 is a spectral intermediate. This inequality does not assert literal four-by-five APPT or settle the unrestricted APPT purity conjecture.

**Theorem 1.2 (Greatest attained spectral purity).**

$$IsGreatest\left(\{p:\mathbb{R}\mid \exists (l:Fin\left(20\right)\to \mathbb{R}),(((Antitone\left(l\right))\land (\forall (i:Fin\left(11 + 9\right)),(0\leq l\left(i\right)))\land (\sum_{i:Fin\left(11 + 9\right)}(l\left(i\right))=1)\land (PosSemidef\left(K1\left(boundaryValues\left(11, l\right)\right)\right))\land (PosSemidef\left(K2\left(boundaryValues\left(11, l\right)\right)\right)))\land (\sum_{i:Fin\left(20\right)}((l\left(i\right))^{2})=p))\}, \frac{7}{121}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound.sharp_spectral_purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value 7/121 is both an upper bound and an attained member of the feasible spectral purity set. Attainment uses (3,1,...,1)/22 with nineteen copies of one. Its boundary pencils coincide and their quadratic form is ((x0-x1)^2+x2^2)/11, so both are positive semidefinite. Its squared mass is (9+19)/22^2=7/121. Attainment is for the stated spectral relaxation; no density-matrix APPT realization is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound.sharp_spectral_purity_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound.spectral_purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound](QutritN6PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN7PurityBound](QutritN7PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer](SpectralBoundaryTransfer.md)
