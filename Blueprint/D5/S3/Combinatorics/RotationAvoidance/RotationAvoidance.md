# RotationAvoidance

## Abstract

Rotation avoidance has exactly eight Wilf classes for patterns of length four.

**Theorem 1.1 (Eight Wilf classes).**

Lean statement: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance.result` (`✓ std3`). ∎

*Resolves.* `Problems/egecioglu-gaiser-yin-rotation-wilf-classes` (proved) by `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"egecioglu-gaiser-yin-rotation-wilf-classes","declaration_gid":"D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu, Collier Gaiser, Mei Yin (2026). *Pattern avoidance in permutations and their rotations*. DOI: [10.48550/arXiv.2607.20750](https://doi.org/10.48550/arXiv.2607.20750). URL: <https://arxiv.org/abs/2607.20750v1>.

*Commentary.*

For every integer k at least four and all patterns q and s that permute one through four, the numbers of permutations of one through n whose first k rotations avoid q and s agree for every n at least k if and only if s is q, its complement, its reverse, or the complement of its reverse. The eight classes are represented by 1234, 1243, 1324, 1342, 1423, 1432, 2143 and 2413. Complement and reversal give equal counts within each orbit; circular counts and strict inequalities between counts of circles with one containing cut separate distinct orbits. Sizes six and seven distinguish the cases k equal to four or five. Classical containment is represented by an increasing choice of values whose pattern-ordered list is a subsequence, as in the order-pattern descriptions used for nonnesting and arrow-decorated permutations.

## References

- Truth anchor: `D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance.result`
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternating](RotationAvoidanceAlternating.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternatingContraction](RotationAvoidanceAlternatingContraction.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacciGap](RotationAvoidanceFibonacciGap.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGaps](RotationAvoidanceGaps.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups](RotationAvoidanceGroups.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredCount](RotationAvoidanceLayeredCount.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayeredEmpty](RotationAvoidanceLayeredEmpty.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry](RotationAvoidanceSymmetry.md)
