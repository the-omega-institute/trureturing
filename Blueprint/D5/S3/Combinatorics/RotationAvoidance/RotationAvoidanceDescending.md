# RotationAvoidanceDescending

## Abstract

The descending consecutive endpoint case has a filtered normal form and an explicit enumeration.

**Theorem 1.1 (Descending consecutive endpoint normal form).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending.descending_consecutive_endpoint_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending.descending_consecutive_endpoint_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a permutation begin with first and end with first plus one. If first is positive and exactly the uncut rotation contains 1432, then first plus three is at most the size. The interior consists of the entries above first plus one, in their original order, followed by the decreasing list of entries below first. The upper filtered list is a permutation of its full interval, avoids 321 and 2143, and is not strictly increasing.

**Theorem 1.2 (Descending consecutive endpoint enumeration).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending.descending_consecutive_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending.descending_consecutive_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For positive first with first plus three at most size, the number of permutations of one through size that begin with first, end with first plus one, and have 1432 in exactly the uncut rotation equals 2 to the power size minus first, minus twice size minus first minus one, minus two, minus the binomial coefficient choosing three from size minus first.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending.descending_consecutive_endpoint_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending.descending_consecutive_endpoint_normal_form`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration](RotationAvoidanceEnumeration.md)
