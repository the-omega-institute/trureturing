# Descending Triples and Direct Sums

## Abstract

Descending endpoints confine triples to a single direct-sum factor, and 312-avoidance orders record blocks.

**Definition 1.1 (A triple with descending endpoints).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.DescendingTriple`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.DescendingTriple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

A descending triple consists of three increasing positions whose first value exceeds their last value and whose values satisfy a specified ternary relation.

**Theorem 1.2 (Triples in a direct sum).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.descendingTriple_sum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.descendingTriple_sum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a ternary relation invariant under adding the same integer to all three values, a direct sum contains a descending triple satisfying that relation exactly when one of its two factors does.

**Theorem 1.3 (Decreasing tails of record blocks).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.avoid312_record_block_decreasing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.avoid312_record_block_decreasing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

In a 312-avoiding permutation, entries strictly after a left-to-right maximum and before the next record boundary decrease with position.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.DescendingTriple`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.avoid312_record_block_decreasing`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumAvoid.descendingTriple_sum_iff`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSum](ThetaBasicSum.md)
