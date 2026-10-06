# RotationAvoidanceSeparated

## Abstract

Separated endpoint configurations force alternating middle normal forms and Fibonacci endpoint structure.

**Theorem 1.1 (Alternating positive middle normal form).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated.alternating_positive_middle_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated.alternating_positive_middle_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let first plus one be less than last and exactly the uncut rotation of a permutation contain 2413. Then first is at least two and last is below size. The interior is the upper filtered list, followed by the middle interval, followed by the lower filtered list. The upper list avoids 213 and 4132, while the lower list avoids 132 and 3241.

**Theorem 1.2 (Fibonacci least endpoint normal form).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated.fibonacci_least_endpoint_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated.fibonacci_least_endpoint_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let a permutation begin with one and end with last, and suppose exactly the uncut rotation contains 1324. Then last is at least four. The interior is the upper filtered list followed by the lower filtered list; these lists are permutations of their corresponding intervals. The upper list avoids 213 and 4132, the lower list avoids 132 and 213, and the lower list is not strictly increasing.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated.alternating_positive_middle_normal_form`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated.fibonacci_least_endpoint_normal_form`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
