# FishburnBasicPrepend

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Insertion positions after prepending the maximum).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnBasicPrepend.prepend_inherited_sites`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnBasicPrepend.prepend_inherited_sites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a Fishburn permutation of positive length n, and let every forbidden pattern belong to the set consisting of 1324, 2143, 1423 and 3124. Prepend n plus one to p. Inserting n plus two at position s plus one in this word, for s from zero through n inclusive, produces an avoiding Fishburn permutation exactly when s is positive, inserting n plus one at position s in p produces an avoiding Fishburn permutation, and, if 3124 is forbidden, every pair of entries in the prefix before s is strictly decreasing.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnBasicPrepend.prepend_inherited_sites`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasic2143](FishburnBasic2143.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicPatternTransport](FishburnBasicPatternTransport.md)
