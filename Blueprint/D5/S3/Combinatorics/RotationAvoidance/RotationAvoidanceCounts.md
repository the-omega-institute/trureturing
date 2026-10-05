# RotationAvoidanceCounts

## Abstract

Cutting a circular permutation at its minimum reduces several classes to classical pattern avoidance and decompositions around the minimum.

**Theorem 1.1 (Three reductions at the minimum).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.minimum_rooted_reductions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.minimum_rooted_reductions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let n be nonnegative and suppose that placing one before a list t gives a permutation of one through n plus one. This permutation is a circular avoider of 1234 exactly when t avoids 123 and 3412; it is a circular avoider of 1342 exactly when t avoids 231, 2134 and 4213; and it is a circular avoider of 1324 exactly when t avoids 213 and 4132.

**Theorem 1.2 (Enumeration of permutations avoiding 213 and 231).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.binary_extreme_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.binary_extreme_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every positive integer n, the number of permutations of one through n avoiding both 213 and 231 is 2^(n - 1). The recurrence for the classical avoidance family removes an extreme first entry; increasing relabelling preserves containment in the smaller family.

**Theorem 1.3 (Decomposition of avoidance of 213 and 4132).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.minimum_split_fibonacci`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.minimum_split_fibonacci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let p be the concatenation of a list L, the entry one and a list R, with no repeated entries and with every entry in L and R greater than one. Then p avoids 213 and 4132 if and only if L avoids both patterns, every entry of R is less than every entry of L, and either L is empty and R avoids both patterns, or L is nonempty and R is strictly increasing.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.binary_extreme_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.minimum_rooted_reductions`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.minimum_split_fibonacci`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanPatterns](../ArcherCyclicPadovanPatterns.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnClassicalDefs](../Fishburn/FishburnClassicalDefs.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
