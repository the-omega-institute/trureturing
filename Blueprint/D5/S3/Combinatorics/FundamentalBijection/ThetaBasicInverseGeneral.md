# Partition into Marked Intervals

## Abstract

Consecutive marked positions partition a word into intervals.

**Definition 1.1 (The next marked boundary).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral.nextBoundary`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral.nextBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Given a predicate on positions, a length n, and a starting position s below n, the next boundary is the least larger position that satisfies the predicate or equals n; for s at least n it is n.

**Theorem 1.2 (Concatenation of consecutive intervals).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral.filter_interval_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral.filter_interval_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

If s is a marked position or the end of a word, concatenating the intervals from each marked position at least s to the next marked boundary recovers the suffix beginning at s.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral.filter_interval_partition`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral.nextBoundary`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks](ThetaBasicInverseBlocks.md)
