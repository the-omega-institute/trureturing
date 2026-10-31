# Dominance for genuine Specht intertwiners

## Abstract

Dominance for genuine Specht intertwiners

A partition mu dominates nu when every prefix sum of the decreasing parts of nu is at most the corresponding prefix sum of mu. For a Young diagram D, S(D) is the existing rational polytabloid span inside its Young permutation module, shape(D) is its literal row partition, and M(nu) is the rational permutation representation on cosets of youngSubgroup nu. Intertwiner(S(D),M(nu)) denotes the full vector space of equivariant rational linear maps. A nonzero such map is injective by the existing atomicity of the Specht span. A preimage of a polytabloid under its column antisymmetrizer then yields the row and column counting inequality. The diagonal and dominance zero statements below consume this implication.

**Theorem 1.1 (A nonzero intertwiner forces dominance).**

$$\forall D \in \operatorname{YoungDiagram},\; \forall nu \in \operatorname{Partition}\left(\operatorname{card}\left(D\right)\right),\; \forall f \in \operatorname{Intertwiner}\left(\operatorname{S}\left(D\right), \operatorname{M}\left(nu\right)\right),\; (f \ne 0) \Rightarrow (\operatorname{Dominates}\left(\operatorname{shape}\left(D\right), nu\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtYoungDominance.dominates_of_intertwiningMap_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The notation has the meanings specified above.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtYoungDominance.dominates_of_intertwiningMap_ne_zero`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility](SpechtAbsoluteIrreducibility.md)
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum](SpechtFixedTabloidPowerSum.md)
