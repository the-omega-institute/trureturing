# RotationAvoidanceAlternating

## Abstract

Separated endpoint intervals give a product of two odd-indexed Fibonacci numbers.

**Theorem 1.1 (Alternating count with separated endpoints).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternating.alternating_positive_middle_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternating.alternating_positive_middle_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let first be at least two, first plus one be less than last, and last be less than size. Among permutations of one through size beginning with first and ending with last, those containing 2413 in exactly the uncut rotation number F_(2(size - last) - 1) times F_(2(first - 1) - 1). The separated lower and upper factors are classical avoidance classes; increasing relabelling preserves pattern containment, and each factor is counted by the odd-indexed Fibonacci enumeration.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternating.alternating_positive_middle_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci](RotationAvoidanceFibonacci.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated](RotationAvoidanceSeparated.md)
