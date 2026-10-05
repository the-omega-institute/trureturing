# RotationAvoidanceAlternatingContraction

## Abstract

Consecutive endpoint contraction counts alternating words by a Fibonacci difference.

**Theorem 1.1 (Alternating count with consecutive endpoints).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternatingContraction.alternating_consecutive_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternatingContraction.alternating_consecutive_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For width at least three and pivot at least two but less than width plus one, permutations of one through width plus two beginning with pivot and ending with pivot plus one, and containing 2413 in exactly the uncut rotation, number F_(2 width - 1) minus F_(2(pivot - 1) - 1) times F_(2(width + 1 - pivot) - 1). Contraction and its increasing inverse relabelling preserve classical containment. The count subtracts the separated circular avoidance class from the full contracted circular class.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternatingContraction.alternating_consecutive_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction](RotationAvoidanceBinaryContraction.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFailureProduct](RotationAvoidanceFailureProduct.md)
