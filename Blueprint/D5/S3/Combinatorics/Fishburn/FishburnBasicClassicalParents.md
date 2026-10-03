# FishburnBasicClassicalParents

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Maximum insertion and deletion).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalParents.classical_maximum_insertion_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalParents.classical_maximum_insertion_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For any collection of classical patterns and any nonnegative n, inserting n plus one gives a bijection from pairs consisting of an avoiding permutation of one through n and an insertion position whose child avoids the same patterns to the avoiding permutations of one through n plus one. Deleting the unique maximum recovers both the parent and its insertion position.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalParents.classical_maximum_insertion_bijection`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnClassicalDefs](FishburnClassicalDefs.md)
