# Crossing Pattern Tests

## Abstract

New occurrences of 2413 and 2431 after maximum insertion are determined by triples crossing the insertion position.

**Theorem 1.1 (Occurrences involving the new maximum).**

Lean statement: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns.maximum_crossing_pattern_tests`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns.maximum_crossing_pattern_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a permutation of one through n and let s be an insertion position from zero through its length. Inserting n + 1 at s gives an occurrence of 2413 exactly when p already contains 2413 or there are positions i, j, k with i less than s, s at most j, j less than k, and k less than the length of p for which the entry at j is less than the entry at i and the entry at i is less than the entry at k. The corresponding criterion for 2431 replaces these value inequalities by the entry at k being less than the entry at i and the entry at i being less than the entry at j. Positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns.maximum_crossing_pattern_tests`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicFourPatterns](../Fishburn/FishburnBasicFourPatterns.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicParents](../Fishburn/FishburnBasicParents.md)
