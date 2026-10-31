# Actual Specht traces paired with Young permutation characters

## Abstract

Actual Specht traces paired with Young permutation characters

The complex Specht module is the independently constructed scalar extension of the literal YoungDiagram.ofPartition polytabloid span. Its character is the trace of its existing action. The Young permutation module is the representation on cosets of the literal Young subgroup. The existing finite-character pairing identifies their pairing with the dimension of the corresponding equivariant Hom space. Inversion preserves a permutation's full cycle partition, so the actual Specht trace takes the same value at a permutation and its inverse.

For n a natural number, mu and nu partitions of n, and pi a permutation of Fin(n), write trace(mu,pi) for the complex trace of the Specht action and fixedTabloids(nu,pi) for the natural cardinality of fixed cosets of youngSubgroup(nu). HomDimension(mu,nu) is the complex finrank of Hom(spechtModuleComplex(mu),permutationModuleComplex(nu)). The displayed finite sum uses every permutation, including those with one-cycles. No character is defined through a polynomial coefficient.

**Theorem 1.1 (Trace pairing with the actual Young permutation representation).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \forall nu \in \operatorname{Partition}\left(n\right),\; \sum_{pi: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)} {\operatorname{trace}\left(mu, pi\right) \operatorname{natCast}\left(\operatorname{fixedTabloids}\left(nu, pi\right), \operatorname{Complex}\right)} = \operatorname{natCast}\left(\operatorname{factorial}\left(n\right), \operatorname{Complex}\right) \operatorname{natCast}\left(\operatorname{HomDimension}\left(mu, nu\right), \operatorname{Complex}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtFrobeniusPairing.sum_spechtTrace_mul_card_fixedPoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

SpechtYoungTrace and SpechtThreeRowMixed consume this identity on the proof route to the literal same-shape trace comparison and both full ordinary weighted endpoints. The exact list-to-partition power-sum transport is also consumed by SpechtThreeRowVirtual and retains repeated parts and every one-cycle. Two former unconsumed polynomial-comparison wrappers are retired. This supplier has no standalone first-freeze claim. The remaining public-declaration audit is tracked at https://github.com/the-omega-institute/trureturing/issues/24542.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtFrobeniusPairing.sum_spechtTrace_mul_card_fixedPoints`
- Dependency: [D5/S3/Combinatorics/Partitions/HemmerStraubWestrem](HemmerStraubWestrem.md)
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum](SpechtFixedTabloidPowerSum.md)
