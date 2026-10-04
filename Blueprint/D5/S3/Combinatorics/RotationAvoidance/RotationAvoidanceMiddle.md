# RotationAvoidanceMiddle

## Abstract

Separated endpoints for 2143 force a five-block increasing normal form.

**Theorem 1.1 (Five-block normal form for separated endpoints).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMiddle.paired_endpoint_middle_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMiddle.paired_endpoint_middle_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let size be at least four and first plus one be less than last. If first followed by interior followed by last permutes one through size and contains 2143 in exactly the uncut rotation, there exist lowerSplit and upperSplit with one at most lowerSplit less than first and upperSplit less than size minus last. The interior concatenates five increasing intervals: the first upperSplit entries above last, the first lowerSplit positive entries, every entry strictly between first and last, the remaining entries above last, and the remaining entries below first.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMiddle.paired_endpoint_middle_normal_form`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent](RotationAvoidanceOneAscent.md)
