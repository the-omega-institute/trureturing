# RotationAvoidanceBinaryContraction

## Abstract

Consecutive endpoint contraction relates circular avoidance to cyclic pattern avoidance and enumerates the resulting binary family.

**Theorem 1.1 (Consecutive endpoint contraction).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction.consecutive_endpoint_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction.consecutive_endpoint_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For a permutation whose first entry is first and whose last entry is first plus one, and for either pattern 2413 or 1342, all rotations contain the pattern only at the uncut position exactly when the interior with the final entry avoids every cyclic rotation of the pattern and the uncut word contains the pattern.

**Theorem 1.2 (Binary count for consecutive endpoints).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction.binary_least_consecutive_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction.binary_least_consecutive_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For width at least three, the number of permutations of one through width plus two that begin with one, end with two, and have 1342 in exactly the uncut rotation is 2 to the width minus width minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction.binary_least_consecutive_endpoint_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceBinaryContraction.consecutive_endpoint_contraction`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear](RotationAvoidanceLinear.md)
