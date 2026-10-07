# RotationAvoidanceAscending

## Abstract

Permutations avoiding 123 and 3412 admit descriptions by a decreasing interval after the minimum and shuffles of the entries below and above that interval.

**Theorem 1.1 (Decomposition of avoidance of 123 and 3412).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.minimum_split_ascending`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.minimum_split_ascending` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let p be the concatenation of a list L, the entry one and a list R, with no repeated entries and with every entry of L and R greater than one. Then p avoids 123 and 3412 if and only if L avoids both patterns, R is strictly decreasing, and every increasing pair of entries in L, taken in their order of appearance, has every entry of R strictly between its two values.

**Theorem 1.2 (The suffix interval and two decreasing subsequences).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.ascending_middle_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.ascending_middle_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Suppose that the concatenation of L, the entry one and R is a permutation of one through n avoiding 123 and 3412, and L is not strictly decreasing. Every integer strictly between two values belonging to R also belongs to R. For every value m in R, the subsequence of L consisting of entries less than m and the subsequence consisting of entries greater than m are both strictly decreasing.

**Theorem 1.3 (Enumeration of shuffles of two separated lists).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.shuffle_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.shuffle_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a Boolean predicate be true on every entry of a list L and false on every entry of a list H. The number of lists that are permutations of the concatenation of L and H and whose subsequences selected by the predicate and its negation are respectively L and H is the binomial coefficient with upper argument the sum of the lengths of L and H and lower argument the length of L. Repeated entries within either list are allowed.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.ascending_middle_interval`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.minimum_split_ascending`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.shuffle_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts](RotationAvoidanceCounts.md)
