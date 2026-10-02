# FishburnBasicClassicalPatterns

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Occurrences created by maximum insertion).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalPatterns.maximum_classical_pattern_tests`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalPatterns.maximum_classical_pattern_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a permutation of one through n, and insert n plus one at a position s between zero and n. The child contains 321 exactly when p already contains 321 or the suffix beginning at s contains a decreasing pair. It contains 231 exactly when p already contains 231 or an entry before s exceeds an entry at or after s. It contains 4132 exactly when p already contains 4132 or the suffix beginning at s contains three entries in increasing positions whose first value is less than the third and whose third value is less than the second.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalPatterns.maximum_classical_pattern_tests`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicInsertion](FishburnBasicInsertion.md)
