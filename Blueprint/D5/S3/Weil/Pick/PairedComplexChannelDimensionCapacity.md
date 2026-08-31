# Paired Complex-Channel Dimension Capacity

## Abstract

Paired complex channels have two complex dimensions of capacity per finite sensor.

**Definition 1.1 (Paired-channel capacity).**

Lean statement: `D5/S3/Weil/Pick/PairedComplexChannelDimensionCapacity.pairedComplexChannelCapacity`

*Formalization.* `D5/S3/Weil/Pick/PairedComplexChannelDimensionCapacity.pairedComplexChannelCapacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The capacity is the finite sensor cardinality multiplied by two, one complex coordinate for each member of the reflected channel pair.

**Theorem 1.2 (Dimension excess forces a blind direction).**

$$\begin{gathered}\forall O \in \operatorname{Hom}_{\mathbb{C}}(V, {I \to \mathbb{C} \times \mathbb{C}}):\\{}(\operatorname{Injective}(O) \Rightarrow \operatorname{finrank}(\mathbb{C}, V) \le \operatorname{pairedComplexChannelCapacity}(I)) \land\\{}(\operatorname{finrank}(\mathbb{C}, V) - \operatorname{pairedComplexChannelCapacity}(I) \le \operatorname{finrank}(\mathbb{C}, \operatorname{ker}(O))) \land\\{}(\operatorname{pairedComplexChannelCapacity}(I) < \operatorname{finrank}(\mathbb{C}, V) \Rightarrow \exists x: V, x \neq 0 \land \operatorname{O}(x) = 0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/PairedComplexChannelDimensionCapacity.paired_complex_channel_dimension_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity into the paired observation codomain bounds the source finrank by the channel capacity. Rank-nullity also gives a quantitative lower bound on the blind-space dimension.

When the source finrank strictly exceeds capacity, noninjectivity produces two distinct states with the same reading. Their difference is an explicit nonzero vector annihilated by every paired channel.

## References

- Truth anchor: `D5/S3/Weil/Pick/PairedComplexChannelDimensionCapacity.pairedComplexChannelCapacity`
- Truth anchor: `D5/S3/Weil/Pick/PairedComplexChannelDimensionCapacity.paired_complex_channel_dimension_capacity`
