# FishburnTenTenAAddresses

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Unique parameters for positive insertion positions).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenAAddresses.a_live_addresses`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenAAddresses.a_live_addresses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For n at least two, consider the increasing permutation, the permutations formed by reversing a consecutive interval from low plus one through high with low plus two at most high and high at most n, and the permutations formed by a decreasing block from peak through bottom plus one, then one, then an increasing block from peak plus one through n, then a decreasing block from bottom through two, where two is at most bottom and bottom is less than peak and peak is at most n. The map from these three disjoint parameter sets to permutations is injective. Its image consists exactly of the Fishburn permutations avoiding 2143, 1423 and 3124 that have a positive insertion position for the next maximum preserving this avoidance.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenAAddresses.a_live_addresses`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnTenTenATree](FishburnTenTenATree.md)
