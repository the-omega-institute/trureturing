# RotationAvoidanceSlices

## Abstract

Endpoint slices for 1324 have a binary factor and an odd-indexed Fibonacci factor.

**Theorem 1.1 (The 1324 count beginning with the minimum).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices.fibonacci_least_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices.fibonacci_least_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For last at least four and at most size, permutations of one through size beginning with one and ending with last, and containing 1324 in exactly the uncut rotation, number (2^(last - 3) - 1) times a factor equal to one when last equals size and to F_(2(size - last) - 1) otherwise. Increasing relabelling preserves containment and separates the classical binary middle factor from the Fibonacci upper factor.

**Theorem 1.2 (An extreme endpoint is necessary for 1324).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices.fibonacci_endpoint_extremality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices.fibonacci_endpoint_extremality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For size at least four, a permutation beginning with first and ending with last that contains 1324 in exactly the uncut rotation must have first equal to one or last equal to size.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices.fibonacci_endpoint_extremality`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices.fibonacci_least_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints](RotationAvoidanceEndpoints.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci](RotationAvoidanceFibonacci.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated](RotationAvoidanceSeparated.md)
