# BouquetHolonomy

## Abstract

Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.

**Theorem 1.1 (transpose state invariance).**

$$\forall (U: \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}), ((\operatorname{conjTranspose}\left(U\right) \times \operatorname{sigma} \times U) .\operatorname{transpose} = \operatorname{sigma}) \Rightarrow \operatorname{conjTranspose}\left(U\right) \times \operatorname{sigma} \times U = \operatorname{sigma}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy.transpose_state_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.2 (two triangle holonomy obstruction).**

$$\forall (U: \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin} 5) \mathbb{C}), (\operatorname{conjTranspose}\left((U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C})\right) \times \operatorname{sigma} \times U = \operatorname{sigma}) \Rightarrow (\operatorname{rho} \operatorname{true} (1 / 1000) \neq (U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}) \times \operatorname{rho} \operatorname{false} (1 / 1000) \times \operatorname{conjTranspose}\left((U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C})\right)) \land (\operatorname{rho} \operatorname{true} (1 / 1000) \neq (U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}) \times (\operatorname{rho} \operatorname{false} (1 / 1000)) .\operatorname{transpose} \times \operatorname{conjTranspose}\left((U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy.two_triangle_holonomy_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cancellation with the distinct diagonal weights and evaluation of the triangle entries exclude both conjugation orientations, providing the obstruction used by bouquet_not_interconvertible.

**Theorem 1.3 (bouquet not interconvertible).**

$$\neg \operatorname{Interconvertible} (\operatorname{rho} \operatorname{false} (1 / 1000)) \operatorname{sigma} (\operatorname{rho} \operatorname{true} (1 / 1000)) \operatorname{sigma}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy.bouquet_not_interconvertible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unitalizing positive trace-preserving interconversion would produce a positive inverse pair fixing the likelihood matrix. Its classification contradicts the two-triangle holonomy obstruction.

## References

- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy.bouquet_not_interconvertible`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy.transpose_state_invariance`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy.two_triangle_holonomy_obstruction`
- Dependency: [D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound](../../Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.md)
- Dependency: [D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseClassification](PositiveInverseClassification.md)
