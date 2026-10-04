# RotationAvoidanceGroups

## Abstract

Representative circular avoidance classes have explicit cardinalities and strict comparisons.

**Theorem 1.1 (Circular representative counts).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups.circular_representative_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups.circular_representative_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For positive size, the circular avoider classes on size plus one entries have the following cardinalities: the 1234 class is 2 to the size plus one minus twice size minus one minus the binomial coefficient choosing three from size plus one; the 1432 and 2143 classes equal it; the 1342 class is 2 to the size minus size; the 1243 class equals the 1342 class; the 1324 class is the Fibonacci number with index twice size minus one; the 1423 and 2413 classes equal the 1324 class. When size is at least five, the 1342 class is smaller than the 1234 class, which is smaller than the 1324 class.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups.circular_representative_counts`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration](RotationAvoidanceEnumeration.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci](RotationAvoidanceFibonacci.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear](RotationAvoidanceLinear.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry](RotationAvoidanceSymmetry.md)
