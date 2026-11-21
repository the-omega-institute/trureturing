# Edge sums on nine blocks of size nine

## Abstract

Edge sums on nine blocks of size nine.

**Theorem 1.1 (Each group element labels one unordered edge).**

$$\mathrm{edgeLabel} : \mathrm{BlockEdge} \to \mathrm{LabelGroup},\quad\operatorname{Bijective}\left(\mathrm{edgeLabel}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineFinite.edgeLabel_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is a block t in the field with nine elements and an unordered pair of distinct vertices in the block. The output is the sum of their labels in the product of two copies of the field and two binary coordinates. The field coordinates fix the midpoint and the block for each displacement up to sign. The binary coordinates distinguish the four displacement classes.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineFinite.edgeLabel_bijective`
