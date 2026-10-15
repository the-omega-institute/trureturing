# Six-level extremality

## Abstract

A supporting functional proves extremality of an absolutely PPT two-qutrit state with six spectral levels.

**Theorem 1.1 (Linearity of the second pencil).**

$$\forall (a:\mathbb{R}), \forall (b:\mathbb{R}), \forall (l:Fin\left(9\right)\to \mathbb{R}), \forall (m:Fin\left(9\right)\to \mathbb{R}), K2\left((SMul.smul\left(a, l\right)+SMul.smul\left(b, m\right))\right)=SMul.smul\left(a, K2\left(l\right)\right)+SMul.smul\left(b, K2\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSixLevelExtremality.K2_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second Hildebrand pencil preserves real linear combinations. The convex-kernel argument and the feasible spectral perturbation use this identity to transport kernel equations.

**Theorem 1.2 (Six spectral levels are attained).**

$$\exists (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), (rho\in Set.extremePoints\left(\mathbb{R}, \{rho\mid ((rho).PosSemidef)\land ((rho).trace=1)\land (APPT\left(rho\right))\}\right))\land ((spectrum\left(\mathbb{C}, rho\right)).ncard=6)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSixLevelExtremality.six_level_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists an extreme absolutely PPT density matrix on two qutrits with exactly six distinct eigenvalues. The diagonal entries of a witness are (318,312,200,169,148,148,130,130,130)/1685. A diagonal supporting functional with weights (-286,-208,-176,128,176,208,242,286,338) forces equality components to coincide.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSixLevelExtremality.K2_linear`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSixLevelExtremality.six_level_attainment`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency](QutritHildebrandSufficiency.md)
