# RotationAvoidanceLinear

## Abstract

The classes avoiding 231, 2134 and 4213 decompose at their maximum into two ordered blocks.

**Theorem 1.1 (Decomposition at the maximum).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear.maximum_split_binary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear.maximum_split_binary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let p be the concatenation of a list L, an entry m and a list R, with no repeated entries and with every entry of L and R less than m. Then p avoids 231, 2134 and 4213 if and only if every entry of L is less than every entry of R, both L and R avoid 213 and 231, and either L is strictly increasing or R is strictly decreasing.

**Theorem 1.2 (Enumeration of permutations avoiding 231, 2134 and 4213).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear.binary_separator_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear.binary_separator_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every nonnegative integer n, the number of permutations of one through n avoiding 231, 2134 and 4213 is 2^n - n. Increasing relabelling preserves containment, and the separated blocks occupy consecutive low and high intervals. The resulting classical avoidance decomposition combines the counts for avoiding 213 and 231.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear.binary_separator_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear.maximum_split_binary`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanBlocks](../ArcherCyclicPadovanBlocks.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts](RotationAvoidanceCounts.md)
