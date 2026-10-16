# Length-twenty spectral purity bound

## Abstract

Every feasible rank-three length-twenty spectrum has purity at most 7/121.

**Theorem 1.1 (Universal spectral inequality).**

$$\forall (l:Fin\left(20\right)\to \mathbb{R}),(((Antitone\left(l\right))\land (\forall (i:Fin\left(11 + 9\right)),(0\leq l\left(i\right)))\land (\sum_{i:Fin\left(11 + 9\right)}(l\left(i\right))=1)\land (PosSemidef\left(K1\left(boundaryValues\left(11, l\right)\right)\right))\land (PosSemidef\left(K2\left(boundaryValues\left(11, l\right)\right)\right)))\Rightarrow (\sum_{i:Fin\left(20\right)}((l\left(i\right))^{2})\leq \frac{7}{121}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound.spectral_purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every antitone nonnegative real spectrum on Fin 20 with mass one and both rank-three boundary matrices positive semidefinite, the square sum is at most 7/121. The baseline-frozen N6 and N7 rational certificate bounds give the endpoints at lengths 18 and 21. N7 exposes its original private certificate without changing its coefficients or proof. The same-delivery new SpectralBoundaryTransfer.spectral_bound_transfer first gives length 19 using a=2, then length 20 using a=1. Expanding this live inference stops at the baseline endpoints, not at the new transfer. Its arbitrary ordered-tuple construction, actual deletion, repeated insertion and normalization provide the structural content of this upper bound. Length 19 is a spectral intermediate. This inequality does not assert literal four-by-five APPT or settle the unrestricted APPT purity conjecture.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound.spectral_purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound](QutritN6PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN7PurityBound](QutritN7PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer](SpectralBoundaryTransfer.md)
