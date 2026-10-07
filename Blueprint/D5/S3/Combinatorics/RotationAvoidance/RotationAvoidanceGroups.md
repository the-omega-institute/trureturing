# RotationAvoidanceGroups

## Abstract

Three circular representative classes have uniformly separated cardinalities.

**Theorem 1.1 (Strict separation of three circular classes).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups.circular_representative_separations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups.circular_representative_separations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For size at least five, the number of circular permutations of one through size plus one rooted at one and avoiding 1342 is strictly smaller than the number avoiding 1234, which is strictly smaller than the number avoiding 1324. Cutting at the minimum and increasing relabelling identify these circular classes with classical avoidance classes. Their counts are 2^size minus size, 2^(size + 1) minus twice size minus one minus the binomial coefficient choosing three from size plus one, and F_(2 size - 1), respectively. Exponential bounds and a Fibonacci recurrence give the strict comparisons.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups.circular_representative_separations`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration](RotationAvoidanceEnumeration.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci](RotationAvoidanceFibonacci.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear](RotationAvoidanceLinear.md)
