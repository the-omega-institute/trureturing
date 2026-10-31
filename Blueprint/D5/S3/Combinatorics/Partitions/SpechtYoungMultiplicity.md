# The diagonal and dominance zeros of Young multiplicities

## Abstract

The diagonal and dominance zeros of Young multiplicities

For a Young diagram D and a partition nu of its number of cells, m(D,nu) is the dimension over the rationals of the actual intertwiner space from the preserved Specht span S(D) to the Young permutation module M(nu). It is zero unless shape(D) dominates nu. On the diagonal, scalar multiplication of the inclusion identifies that intertwiner space with the rationals, giving dimension one. The proof uses the actual column antisymmetrizer, its preimage in the Specht span, and the orbit spanning property of a polytabloid. These results supply the triangular part of Young rule; they do not identify the other entries with Kostka numbers.

**Theorem 1.1 (The dominance zero region).**

$$\forall D \in \operatorname{YoungDiagram},\; \forall nu \in \operatorname{Partition}\left(\operatorname{card}\left(D\right)\right),\; (\operatorname{Not}\left(\operatorname{Dominates}\left(\operatorname{shape}\left(D\right), nu\right)\right)) \Rightarrow (\operatorname{m}\left(D, nu\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtYoungMultiplicity.spechtMultiplicity_eq_zero_of_not_dominates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The notation has the meanings specified above.

**Theorem 1.2 (The actual diagonal dimension).**

$$\forall D \in \operatorname{YoungDiagram},\; \operatorname{m}\left(D, \operatorname{shape}\left(D\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtYoungMultiplicity.spechtMultiplicity_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The notation has the meanings specified above.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtYoungMultiplicity.spechtMultiplicity_eq_zero_of_not_dominates`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtYoungMultiplicity.spechtMultiplicity_self`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtYoungDominance](SpechtYoungDominance.md)
