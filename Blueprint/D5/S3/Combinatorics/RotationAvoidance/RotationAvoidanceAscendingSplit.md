# RotationAvoidanceAscendingSplit

## Abstract

Nonextreme ascending endpoints are enumerated by permutations with one ascent.

**Theorem 1.1 (Ascending count with nonextreme endpoints).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingSplit.ascending_nonextreme_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingSplit.ascending_nonextreme_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let first be positive, first plus two be less than last, and last be at most size, with first greater than one or last less than size. Permutations of one through size beginning with first and ending with last, and containing 1234 in exactly the uncut rotation, number 2^(last - first - 1) minus (last - first - 1) minus one. The fixed outside blocks leave a middle permutation with exactly one ascent.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingSplit.ascending_nonextreme_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingOutside](RotationAvoidanceAscendingOutside.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent](RotationAvoidanceOneAscent.md)
