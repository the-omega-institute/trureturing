# Six-level extremality

## Abstract

A supporting functional proves extremality of an absolutely PPT two-qutrit state with six spectral levels.

**Theorem 1.1 (Six spectral levels are attained).**

$$\exists (rho:Matrix\left((Fin\left(3\right)\times Fin\left(3\right)), (Fin\left(3\right)\times Fin\left(3\right)), \mathbb{C}\right)), (rho\in Set.extremePoints\left(\mathbb{R}, \{rho\mid ((rho).PosSemidef)\land ((rho).trace=1)\land (APPT\left(rho\right))\}\right))\land ((spectrum\left(\mathbb{C}, rho\right)).ncard=6)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSixLevelExtremality.six_level_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists an extreme absolutely PPT density matrix on two qutrits with exactly six distinct eigenvalues. The diagonal entries of a witness are (318,312,200,169,148,148,130,130,130)/1685. A diagonal supporting functional with weights (-286,-208,-176,128,176,208,242,286,338) forces equality components to coincide.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSixLevelExtremality.six_level_attainment`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency](QutritHildebrandSufficiency.md)
