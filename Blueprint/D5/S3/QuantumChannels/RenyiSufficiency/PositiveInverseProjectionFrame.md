# PositiveInverseProjectionFrame

## Abstract

Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.

**Theorem 1.1 (orthogonal projection frame).**

$$\forall (n: \mathbb{N}), \forall (P: \operatorname{Fin} n \to \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (\forall i , (P i) .\operatorname{IsHermitian}) \Rightarrow (\forall i , P i \neq 0) \Rightarrow (\forall i , P i \times P i = P i) \Rightarrow (\forall i j , i \neq j \to P i \times P j = 0) \Rightarrow \exists U : \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin} n) \mathbb{C} , \forall i , P i = (U : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) \times \operatorname{single} i i 1 \times \operatorname{conjTranspose}\left((U : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame.orthogonal_projection_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonzero mutually orthogonal Hermitian projections give a unit vector in each range. These vectors form the columns of the unitary matrix U.

**Theorem 1.2 (positive inverse projection alignment).**

$$\forall (n: \mathbb{N}), \forall (Phi: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (Psi: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (\operatorname{IsPositive} Phi) \Rightarrow (\operatorname{IsPositive} Psi) \Rightarrow (Phi 1 = 1) \Rightarrow (Psi 1 = 1) \Rightarrow (Psi.\operatorname{comp} Phi = \operatorname{LinearMap}.\operatorname{id}) \Rightarrow \exists U : \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin} n) \mathbb{C} , \forall i , Phi (\operatorname{single} i i 1) = (U : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) \times \operatorname{single} i i 1 \times \operatorname{conjTranspose}\left((U : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame.positive_inverse_projection_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

## References

- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame.orthogonal_projection_frame`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame.positive_inverse_projection_alignment`
- Dependency: [D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain](PositiveMapJordanDomain.md)
