# Indecomposability after Maximum Insertion

## Abstract

Inserting a new maximum destroys direct-sum boundaries precisely when each preceding boundary has an inversion across it.

**Theorem 1.1 (The boundary criterion).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSumInsertion.indecomposable_maximum_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSumInsertion.indecomposable_maximum_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a permutation of one through n and let s be an insertion position from zero through its length. Inserting n + 1 at s produces a sum-indecomposable permutation if and only if, for every boundary b with zero less than b and b at most s, there are positions i and j with i less than b, b at most j, and j less than the length of p such that the entry at j is at most the entry at i. Positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSumInsertion.indecomposable_maximum_insertion`
- Dependency: [D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponents](FishburnBasicComponents.md)
