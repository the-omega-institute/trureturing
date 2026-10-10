# BouquetFixedPoint

## Abstract

Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.

**Theorem 1.1 (mu mul).**

$$\forall (i: \operatorname{Fin} 5), \forall (j: \operatorname{Fin} 5), \forall (k: \operatorname{Fin} 5), \forall (l: \operatorname{Fin} 5), (\operatorname{single} i j (1 : \mathbb{C})) \times (\operatorname{single} k l (1 : \mathbb{C})) = \operatorname{if} j = k \operatorname{then} (\operatorname{single} i l (1 : \mathbb{C})) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint.mu_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.2 (jordan projector edge).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin} n), \forall (j: \operatorname{Fin} n), (i \neq j) \Rightarrow \forall (Y: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \operatorname{jordan} (\operatorname{single} i i 1) (\operatorname{jordan} (\operatorname{single} j j 1) Y) = Y i j \cdot \operatorname{single} i j 1 + Y j i \cdot \operatorname{single} j i 1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint.jordan_projector_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.3 (bouquet fixed point rigidity).**

$$\forall (E: \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} 5) (\operatorname{Fin} 5) \mathbb{C}), (\operatorname{IsPositive} E) \Rightarrow (E 1 = 1) \Rightarrow (\forall Y , (\operatorname{sigma} \times E Y) .\operatorname{trace} = (\operatorname{sigma} \times Y) .\operatorname{trace}) \Rightarrow (E (\operatorname{likelihood} \operatorname{false}) = \operatorname{likelihood} \operatorname{false}) \Rightarrow E = \operatorname{LinearMap}.\operatorname{id}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint.bouquet_fixed_point_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The likelihood spectral projectors force trace preservation, which fixes sigma. Sigma projectors isolate the bouquet edges, and their Jordan closure generates every matrix unit.

## References

- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint.bouquet_fixed_point_rigidity`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint.jordan_projector_edge`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint.mu_mul`
- Dependency: [D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum](LikelihoodSpectrum.md)
- Dependency: [D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain](PositiveMapJordanDomain.md)
