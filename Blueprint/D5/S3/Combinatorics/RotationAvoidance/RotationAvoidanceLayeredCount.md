# RotationAvoidanceLayeredCount

## Abstract

A layered endpoint class with nonempty lower interval has a Fibonacci product count.

**Theorem 1.1 (Layered count with nonempty lower interval).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredCount.layered_nonempty_lower_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredCount.layered_nonempty_lower_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let first be at least two, first plus one be less than last, and last be less than size. Permutations of one through size beginning with first and ending with last, and containing 1423 in exactly the uncut rotation, number F_(2(size - last) - 1) times F_(2(first - 1) - 1). The lower and upper factors are classical avoidance classes. Complementing the lower interval and increasing relabelling of the upper interval reduce both factors to the odd-indexed Fibonacci enumeration.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredCount.layered_nonempty_lower_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci](RotationAvoidanceFibonacci.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayered](RotationAvoidanceLayered.md)
