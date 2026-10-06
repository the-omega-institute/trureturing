# RotationAvoidanceMixedEmpty

## Abstract

When the lower block is empty, the mixed pattern has a rigid filtered form or a single split parameter.

**Theorem 1.1 (Mixed empty lower normal form).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmpty.mixed_empty_lower_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmpty.mixed_empty_lower_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a permutation begin with one and end with last, with last greater than one. If exactly the uncut rotation contains 1243, then last is greater than two and below size. The entries below last in the interior form the reverse interval from two through last minus one. Either the upper filtered list is the interval above last and the interior is not the concatenation of that upper interval with the lower reverse interval, or there is a split between one and size minus last that gives the interior as an upper interval, the lower reverse interval, and a final upper interval.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmpty.mixed_empty_lower_normal_form`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
