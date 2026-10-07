# RotationAvoidanceConsecutive

## Abstract

The 2143 endpoint classes are counted by shuffles and independent interval splits.

**Theorem 1.1 (Consecutive endpoints and a binomial count).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive.consecutive_shuffle_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive.consecutive_shuffle_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For positive lowerCount and upperCount, permutations of one through lowerCount plus upperCount plus two beginning with lowerCount plus one and ending with lowerCount plus two, and containing 2143 in exactly the uncut rotation, number the binomial coefficient choosing lowerCount from lowerCount plus upperCount, minus one. Their interiors shuffle two increasing intervals; the ordered concatenation is excluded.

**Theorem 1.2 (Separated endpoints and a product count).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive.positive_middle_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive.positive_middle_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let first be at least two, first plus one be less than last, and last be less than size. Permutations of one through size beginning with first and ending with last, and containing 2143 in exactly the uncut rotation, number (first - 1) times (size - last). The normal form is determined by an independent split in each of the lower and upper intervals.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive.consecutive_shuffle_endpoint_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive.positive_middle_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMiddle](RotationAvoidanceMiddle.md)
