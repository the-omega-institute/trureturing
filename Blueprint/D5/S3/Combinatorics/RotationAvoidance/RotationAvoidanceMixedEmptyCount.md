# RotationAvoidanceMixedEmptyCount

## Abstract

The mixed endpoint class with empty lower interval has a binomial count.

**Theorem 1.1 (Mixed count with empty lower interval).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmptyCount.mixed_empty_lower_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmptyCount.mixed_empty_lower_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For last greater than two and less than size, permutations of one through size beginning with one and ending with last, and containing 1243 in exactly the uncut rotation, number the binomial coefficient choosing last minus two from size minus two, plus (size - last), minus two. The normal form combines a shuffle of decreasing intervals with the remaining split cases.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmptyCount.mixed_empty_lower_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending](RotationAvoidanceAscending.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmpty](RotationAvoidanceMixedEmpty.md)
