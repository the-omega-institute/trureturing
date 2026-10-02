# FishburnTenSevenMinimum

## Abstract

Occurrences of four patterns in a Fishburn permutation can be placed relative to its minimum.

**Theorem 1.1 (Pattern tests around one).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum.minimum_pattern_tests`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum.minimum_pattern_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a Fishburn permutation of one through n, and let one be the position of its entry one. An occurrence of 1324 exists if and only if three positions after one form 213, and an occurrence of 1423 exists if and only if three positions after one form 312. If p avoids 1324, an occurrence of 2143 exists if and only if positions first, second and third with first before one and one before second before third have the entry at first below that at third below that at second. Under the same avoidance assumption, an occurrence of 3124 exists if and only if such positions have the entry at second below that at first below that at third.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum.minimum_pattern_tests`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicDecreasingPrefixes](../Fishburn/FishburnBasicDecreasingPrefixes.md)
