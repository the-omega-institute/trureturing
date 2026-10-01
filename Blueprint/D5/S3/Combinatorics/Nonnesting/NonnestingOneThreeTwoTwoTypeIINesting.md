# Nonnesting under Type II Insertion

## Abstract

Type II insertion preserves avoidance of both nesting patterns.

**Theorem 1.1 (Type II preserves nonnesting).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeIINesting.typeII_nonnesting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeIINesting.typeII_nonnesting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Suppose every upper letter exceeds the pivot, every letter of the lower order is smaller than the pivot, the upper word has exactly two copies of each of its letters, and the lower order has distinct entries. If the upper word and the concatenation of two copies of the lower order avoid 1221 and 2112, and every first occurrence in the upper word lies before the cut, the type II word also avoids 1221 and 2112.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeIINesting.typeII_nonnesting`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII](NonnestingOneThreeTwoTwoTypeII.md)
