# Actual Matching Representatives for Every Partition

## Abstract

Every partition is realized by an actual native matching with its complete coset type.

**Theorem 1.1 (All Partitions Have Native Representatives).**

$$\forall k \in Nat,\; \forall rho \in \operatorname{Partition}\left(k\right),\; \exists p \in \operatorname{P}\left(k\right),\; \operatorname{ct}\left(p\right) = rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRealization.matching_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a permutation with the prescribed parts at least two as its ordinary cycle type. The full SameCycle partition also contains every fixed singleton orbit. Its nontrivial blocks correspond bijectively to cycle factor supports. A positive multiset is reconstructed from those blocks and its total sum, restoring exactly the required singleton multiplicity. The canonical oriented construction turns the permutation into a fixed-point-free involutive partner map on Fin(2k); the existing ct_oriented theorem identifies its complete type. The argument includes k=0 and all repeated parts.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRealization.matching_realization`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyComponents](DeformedJucysMurphyComponents.md)
