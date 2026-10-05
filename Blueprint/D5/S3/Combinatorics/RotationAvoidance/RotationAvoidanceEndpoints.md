# RotationAvoidanceEndpoints

## Abstract

Extreme endpoints reduce unique containing cuts to classical avoidance counts.

**Theorem 1.1 (Ascending count with extreme endpoints).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints.ascending_extreme_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints.ascending_extreme_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For width at least two, permutations of one through width plus two beginning with one and ending with width plus two, and containing 1234 in exactly the uncut rotation, number 2^(width + 1) minus twice width minus two minus the binomial coefficient choosing three from width plus one. Increasing relabelling identifies the interior with the classical class avoiding 123 and 3412, with its decreasing permutation removed.

**Theorem 1.2 (The 1324 count with extreme endpoints).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints.fibonacci_extreme_endpoint_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints.fibonacci_extreme_endpoint_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For width at least two, permutations of one through width plus two beginning with one and ending with width plus two, and containing 1324 in exactly the uncut rotation, number 2^(width - 1) minus one. Increasing relabelling identifies the interior with permutations avoiding 132 and 213, with its increasing permutation removed.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints.ascending_extreme_endpoint_count`
- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEndpoints.fibonacci_extreme_endpoint_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups](RotationAvoidanceGroups.md)
