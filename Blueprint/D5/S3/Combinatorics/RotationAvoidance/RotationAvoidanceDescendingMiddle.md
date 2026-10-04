# RotationAvoidanceDescendingMiddle

## Abstract

A descending pattern with a separated middle endpoint yields increasing upper pieces and a lower suffix.

**Theorem 1.1 (Descending positive middle normal form).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingMiddle.descending_positive_middle_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingMiddle.descending_positive_middle_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a permutation begin with first, end with last, and have first plus one less than last. If exactly the uncut rotation contains 1432, then last plus two is at most size. The interior is an increasing list of upper values, followed by the consecutive middle interval, followed by a suffix and the increasing list of values below first. The upper list and suffix together contain all values above last, each of the two displayed outer pieces is increasing, and some upper value exceeds some lower value in the suffix.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingMiddle.descending_positive_middle_normal_form`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
