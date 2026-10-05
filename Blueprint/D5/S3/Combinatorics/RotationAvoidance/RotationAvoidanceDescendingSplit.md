# RotationAvoidanceDescendingSplit

## Abstract

Separated endpoints for 1432 leave an upper interval with one ascent.

**Theorem 1.1 (Descending count with separated endpoints).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingSplit.descending_positive_middle_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingSplit.descending_positive_middle_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let first be positive, first plus one be less than last, and last plus two be at most size. Permutations of one through size beginning with first and ending with last, and containing 1432 in exactly the uncut rotation, number 2^(size - last) minus (size - last) minus one. The normal form reduces the choice to two decreasing upper blocks whose concatenation has exactly one ascent.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingSplit.descending_positive_middle_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingMiddle](RotationAvoidanceDescendingMiddle.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent](RotationAvoidanceOneAscent.md)
