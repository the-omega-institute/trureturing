# Assemble subgroup-local permutations into one distinct-power enumeration

## Abstract

Assemble subgroup-local permutations into one distinct-power enumeration.

**Theorem 1.1 (claim_of_orderFour).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Assembly.claim_of_orderFour`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Assembly.claim_of_orderFour` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dingying Ma (2026). *On Distinct Powers in Finite Groups*. DOI: [10.48550/arXiv.2611.13582](https://doi.org/10.48550/arXiv.2611.13582). URL: <https://arxiv.org/abs/2611.13582v1>.

*Commentary.*

Group elements by the cyclic subgroups they generate, and then by class size. The slot map fills the indices and the local permutations ensure distinct powers within classes. Preservation of generated subgroups separates powers from different classes. The final result supplies the order-four premise.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Assembly.claim_of_orderFour`
- Dependency: [D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Allocation](Allocation.md)
- Dependency: [D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers](LocalPowers.md)
