# RotationAvoidanceEnumeration

## Abstract

The permutations avoiding 123 and 3412 are enumerated by separating decreasing prefixes from prefixes containing an ascent.

**Theorem 1.1 (Enumeration with a fixed position of the minimum).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_positive_suffix_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_positive_suffix_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For a nonnegative integer w and a positive integer s, consider permutations of one through w plus s plus one that avoid 123 and 3412, have exactly w entries before one and have a prefix before one that is not strictly decreasing. Their number is 2^w - w - 1.

**Theorem 1.2 (Enumeration with a decreasing prefix before the minimum).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_decreasing_prefix_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_decreasing_prefix_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every nonnegative integer s, the number of permutations of one through s plus one avoiding 123 and 3412 whose prefix before one is strictly decreasing is 2^s. An empty prefix is permitted.

**Theorem 1.3 (Enumeration of permutations avoiding 123 and 3412).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every nonnegative integer n, the number of permutations of one through n avoiding 123 and 3412 is 2^(n + 1) - 2n - 1 - C(n + 1, 3), where C(n + 1, 3) is the binomial coefficient with upper argument n plus one and lower argument three. All subtractions are natural-number subtractions.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_decreasing_prefix_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.ascending_positive_suffix_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending](RotationAvoidanceAscending.md)
