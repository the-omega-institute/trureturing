# RotationAvoidanceFibonacciGap

## Abstract

The 1324 and 1423 classes with one containing cut have different cardinalities.

**Theorem 1.1 (Strict inequality from the Fibonacci class to the layered class).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacciGap.fibonacci_lt_layered`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacciGap.fibonacci_lt_layered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every size at least seven, the number of circular permutations rooted at one with exactly one rotation containing 1324 is strictly less than the corresponding number for 1423. Endpoint decompositions express both totals through odd-indexed Fibonacci factors and binomial counts; comparison of these sums gives the strict inequality.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacciGap.fibonacci_lt_layered`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternating](RotationAvoidanceAlternating.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternatingContraction](RotationAvoidanceAlternatingContraction.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredCount](RotationAvoidanceLayeredCount.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredEmpty](RotationAvoidanceLayeredEmpty.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed](RotationAvoidanceMixed.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmptyCount](RotationAvoidanceMixedEmptyCount.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSlices](RotationAvoidanceSlices.md)
