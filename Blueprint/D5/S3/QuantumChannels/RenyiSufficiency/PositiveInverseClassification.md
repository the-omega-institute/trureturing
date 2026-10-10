# PositiveInverseClassification

## Abstract

Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.

**Theorem 1.1 (unital positive inverse classification).**

$$\forall (Phi: \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}), \forall (Psi: \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}), (\operatorname{IsPositive} Phi) \Rightarrow (\operatorname{IsPositive} Psi) \Rightarrow (Phi 1 = 1) \Rightarrow (Psi 1 = 1) \Rightarrow (Psi.\operatorname{comp} Phi = \operatorname{LinearMap}.\operatorname{id}) \Rightarrow \exists U : \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin} 5) \mathbb{C} , (\forall Y , Phi Y = (U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}) \times Y \times \operatorname{star} (U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C})) \lor (\forall Y , Phi Y = (U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}) \times Y.\operatorname{transpose} \times \operatorname{star} (U : \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseClassification.unital_positive_inverse_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After aligning the diagonal projections, the Jordan identity confines each matrix unit to its two Peirce orientations. Their common orientation and phases produce a unitary or transpose-unitary conjugation.

## References

- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseClassification.unital_positive_inverse_classification`
- Dependency: [D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint](BouquetFixedPoint.md)
- Dependency: [D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame](PositiveInverseProjectionFrame.md)
