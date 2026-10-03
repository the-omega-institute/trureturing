# RotationAvoidanceCircular

## Abstract

Circular permutations represented with the entry one first relate avoidance at all cuts to avoidance of cyclic rotations of a pattern.

**Definition 1.1 (Circular avoiders rooted at one).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.circularAvoiders`

*Formalization.* `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.circularAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For a nonnegative integer n and a pattern q, the circular avoiders are those permutations of one through n whose first entry is one and whose n rotations all avoid q.

**Definition 1.2 (Circles with exactly one containing cut).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.singleBadCircles`

*Formalization.* `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.singleBadCircles` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For a nonnegative integer n and a pattern q, this set consists of permutations of one through n beginning with one for which there exists exactly one cut among zero through n minus one whose rotation contains q. Every other cut avoids q.

**Theorem 1.3 (Counting full and all but one rotation avoidance).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.counting_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.counting_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let n be positive and let q be any pattern. The cardinality of S_n^(n)(q) is n times the number of circular avoiders rooted at one. The cardinality of S_n^(n minus one)(q) is n times that number plus the number of circles rooted at one with exactly one containing cut.

**Theorem 1.4 (Characterization of a unique containing cut).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.unique_bad_cut_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.unique_bad_cut_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let n be at least four, let q be a permutation of one through four and let p be a permutation of one through n. Cut zero is the unique cut whose rotation contains q if and only if p contains q, p avoids each of the three nontrivial cyclic rotations of q, and deleting either the first entry or the last entry of p gives a list avoiding q.

**Theorem 1.5 (Circular avoidance and the rotations of a pattern).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.all_cuts_iff_cycle_avoidance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.all_cuts_iff_cycle_avoidance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

Let n be positive, let q be a permutation of one through four and let p be a permutation of one through n. All n rotations of p avoid q if and only if p avoids all four cyclic rotations of q.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.all_cuts_iff_cycle_avoidance`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.circularAvoiders`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.counting_cuts`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.singleBadCircles`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.unique_bad_cut_iff`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs](RotationAvoidanceDefs.md)
