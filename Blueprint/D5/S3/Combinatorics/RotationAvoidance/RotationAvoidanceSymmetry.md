# RotationAvoidanceSymmetry

## Abstract

Complement and reverse preserve the cardinalities of permutation classes defined by avoidance in the first k rotations.

**Theorem 1.1 (Wilf equivalence within an orbit).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry.orbit_wilfEquivalent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry.orbit_wilfEquivalent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every positive integer k, every permutation q of one through four and every pattern s in the complement and reverse orbit of q, the patterns q and s are Wilf-equivalent for k rotations. Thus S_n^(k)(q) and S_n^(k)(s) have equal cardinalities for every n at least k.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry.orbit_wilfEquivalent`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs](RotationAvoidanceDefs.md)
