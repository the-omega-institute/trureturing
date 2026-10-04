# RotationAvoidanceLayered

## Abstract

The layered endpoint case decomposes into four blocks with order and avoidance constraints.

**Theorem 1.1 (Layered endpoint normal form).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayered.layered_endpoint_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayered.layered_endpoint_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a permutation begin with first, end with last, and have first less than last. If exactly the uncut rotation contains 1423, then first plus one is less than last and last is below size. The interior splits into before, upper, lower and suffix blocks: upper and lower are permutations of the values above last and below first, while before with suffix contains the middle values. Both outer blocks are decreasing, every suffix value is below every before value, the suffix is nonempty, and if first is at least two then before is empty. The upper block avoids 312 and 2314, and the lower block avoids 231 and 1423.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayered.layered_endpoint_normal_form`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
