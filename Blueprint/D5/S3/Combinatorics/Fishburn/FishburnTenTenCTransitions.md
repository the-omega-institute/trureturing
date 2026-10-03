# FishburnTenTenCTransitions

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Transitions in the second classical class).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTransitions.c_insertion_transitions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTransitions.c_insertion_transitions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a permutation of length n avoiding 231, 4132 and 2134, and suppose insertion of n plus one at position s from zero through n preserves these conditions. Inserting n plus two into the child at a position g from zero through n plus one preserves the conditions exactly in one of three cases: s equals n, g is at most n, and insertion of n plus one at g in p is permitted; s is less than n and g equals s; or g equals n plus one, appending n plus one to p is permitted, and the prefix of p before s is strictly increasing.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTransitions.c_insertion_transitions`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalPatterns](FishburnBasicClassicalPatterns.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicFourPatterns](FishburnBasicFourPatterns.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnClassicalDefs](FishburnClassicalDefs.md)
