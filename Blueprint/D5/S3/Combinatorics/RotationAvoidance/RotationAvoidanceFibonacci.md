# RotationAvoidanceFibonacci

## Abstract

Two classical pattern avoidance classes have cardinalities given by odd-indexed Fibonacci numbers and powers of two.

**Theorem 1.1 (Enumeration of permutations avoiding 213 and 4132).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci.fibonacci_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci.fibonacci_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every positive integer n, the number of permutations of one through n avoiding 213 and 4132 is F_(2n minus one), where F_0 is zero, F_1 is one and each subsequent Fibonacci number is the sum of the preceding two. Decomposition at the minimum uses the classical avoidance family, invariance of containment under increasing relabelling, and the fact that separated low and high blocks have interval supports.

**Theorem 1.2 (Enumeration of permutations avoiding 132 and 213).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci.skew_block_binary_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci.skew_block_binary_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every positive integer n, the number of permutations of one through n avoiding both 132 and 213 is 2^(n - 1). Permutations avoiding 132 and 213 are concatenations of increasing interval blocks ordered from high values to low values. The increasing-block characterization and its converse identify such permutations with compositions of n.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci.fibonacci_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci.skew_block_binary_count`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanBlocks](../ArcherCyclicPadovanBlocks.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncConverse](../Nonnesting/NonnestingBasicRoyalIncConverse.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts](RotationAvoidanceCounts.md)
