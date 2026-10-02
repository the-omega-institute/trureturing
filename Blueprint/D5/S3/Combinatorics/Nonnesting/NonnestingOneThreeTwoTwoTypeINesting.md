# Nonnesting under Type I Insertion

## Abstract

Type I insertion preserves avoidance of both nesting patterns.

**Theorem 1.1 (Type I preserves nonnesting).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeINesting.typeI_nonnesting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeINesting.typeI_nonnesting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Suppose every upper letter exceeds the pivot, every lower letter is smaller than the pivot, the lower word has exactly two copies of each of its letters, and both words avoid 1221 and 2112. If every first occurrence in the lower word lies before the cut, the type I word also avoids 1221 and 2112.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeINesting.typeI_nonnesting`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoPartition](NonnestingOneThreeTwoTwoPartition.md)
