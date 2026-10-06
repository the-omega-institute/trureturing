# RotationAvoidanceMixed

## Abstract

The mixed pattern with a nonempty lower part forces adjacent endpoints and has a binomial enumeration.

**Theorem 1.1 (Mixed nonempty lower normal form).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed.mixed_nonempty_lower_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed.mixed_nonempty_lower_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a permutation begin with first, end with last, and have first at least two and first less than last. If exactly the uncut rotation contains 1243, then last equals first plus two and is below size. The interior begins with first plus one, followed by a list whose values are exactly those below first or above last. The lower filtered subsequence is decreasing and the upper filtered subsequence is increasing.

**Theorem 1.2 (Mixed nonempty lower endpoint enumeration).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed.mixed_nonempty_lower_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed.mixed_nonempty_lower_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For first at least two and first plus two below size, the number of permutations of one through size that begin with first, end with first plus two, and have 1243 in exactly the uncut rotation is the binomial coefficient choosing first minus one from size minus three.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed.mixed_nonempty_lower_endpoint_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed.mixed_nonempty_lower_normal_form`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending](RotationAvoidanceAscending.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
