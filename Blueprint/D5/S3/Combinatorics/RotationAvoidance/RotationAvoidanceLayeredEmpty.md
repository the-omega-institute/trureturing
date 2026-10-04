# RotationAvoidanceLayeredEmpty

## Abstract

A layered endpoint class beginning at the minimum has one interval split and a Fibonacci factor.

**Theorem 1.1 (Layered count with empty lower interval).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredEmpty.layered_empty_lower_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredEmpty.layered_empty_lower_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For last greater than two and less than size, permutations of one through size beginning with one and ending with last, and containing 1423 in exactly the uncut rotation, number (last - 2) times F_(2(size - last) - 1). The middle interval has last minus two possible splits, while increasing relabelling identifies the upper factor with the classical Fibonacci avoidance class.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredEmpty.layered_empty_lower_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci](RotationAvoidanceFibonacci.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayered](RotationAvoidanceLayered.md)
