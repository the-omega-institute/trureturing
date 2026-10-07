# RotationAvoidanceFailureProduct

## Abstract

Separated alternating circles factor into two Fibonacci enumerations.

**Theorem 1.1 (Separated alternating circle count).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFailureProduct.alternating_separated_circle_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFailureProduct.alternating_separated_circle_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For a pivot between two and size minus one, consider circular avoiders of 2413 rooted at pivot whose tail is all entries below pivot followed by all entries above pivot. Their number is the product of the Fibonacci numbers with indices twice pivot minus three and twice size minus pivot minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFailureProduct.alternating_separated_circle_count`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular](RotationAvoidanceCircular.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci](RotationAvoidanceFibonacci.md)
