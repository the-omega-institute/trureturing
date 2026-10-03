# FishburnTenTenCCount

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Enumeration of the second classical class).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCCount.c_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenCCount.c_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

There is one empty permutation avoiding 231, 4132 and 2134. For every positive n, the number of permutations of length n avoiding these patterns is n plus twice the binomial coefficient choosing three from n.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCCount.c_enumeration`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree](FishburnTenTenCTree.md)
