# RotationAvoidanceDefs

## Abstract

Permutations whose first k rotations avoid a fixed pattern are compared by their cardinalities and the complement and reverse symmetries of patterns of length four.

**Definition 1.1 (Avoidance in the first k rotations).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.rotationAvoiders`

*Formalization.* `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.rotationAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For nonnegative integers n and k and a pattern q, the set S_n^(k)(q) consists of permutations of one through n such that rotating the first i entries to the end avoids q for every nonnegative i less than k. Pattern avoidance is classical avoidance.

**Definition 1.2 (Wilf equivalence for a fixed number of rotations).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.WilfEquivalent`

*Formalization.* `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.WilfEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Patterns q and s are Wilf-equivalent for k rotations when S_n^(k)(q) and S_n^(k)(s) have equal cardinalities for every nonnegative integer n at least k.

**Definition 1.3 (Complement of a pattern of length four).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.complement`

*Formalization.* `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.complement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

The complement of a pattern of length four replaces each entry x by five minus x, preserving the order of its positions. More generally, this operation is defined on lists of natural numbers using natural-number subtraction.

**Definition 1.4 (Complement and reverse orbit).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.orbit`

*Formalization.* `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.orbit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

The complement and reverse orbit of q is the set consisting of q, its complement, its reverse and the complement of its reverse.

**Definition 1.5 (Statement of Open Question 6.1).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.claim`

*Formalization.* `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Open Question 6.1 asks whether, for every integer k at least four and every pair q and s of permutations of one through four, Wilf equivalence for k rotations holds if and only if s belongs to the complement and reverse orbit of q. The proposition expresses the conjectured classification into eight orbits; it does not assert that this classification holds.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.WilfEquivalent`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.complement`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.orbit`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.rotationAvoiders`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingDefs](../Nonnesting/NonnestingDefs.md)
