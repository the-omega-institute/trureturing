# Prefix Partition for 1322 Avoidance

## Abstract

The prefix before a pivot separates larger letters from smaller letters.

**Theorem 1.1 (Partition before the first pivot).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoPartition.prefix_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoPartition.prefix_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

In a word containing exactly two copies of each of its letters and avoiding 1322, the prefix before the first occurrence of any pivot equals its subsequence of letters larger than the pivot followed by its subsequence of letters smaller than the pivot.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoPartition.prefix_partition`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI](NonnestingOneThreeTwoTwoTypeI.md)
