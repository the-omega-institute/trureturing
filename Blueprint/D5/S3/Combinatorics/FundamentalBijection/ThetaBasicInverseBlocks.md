# Cycles from Record Blocks

## Abstract

The inverse fundamental bijection closes consecutive record blocks into cycles.

**Theorem 1.1 (The cycle of a record maximum).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks.cycleFrom_B_record_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks.cycleFrom_B_record_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a permutation p, a block beginning at a left-to-right maximum and ending immediately before the next such maximum, or at the end of p, is exactly the cycle of its initial value in the inverse image of p.

**Theorem 1.2 (Cycle maxima are record values).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks.nonrecord_not_B_leader`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks.nonrecord_not_B_leader` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

A letter whose position in a permutation is not a left-to-right maximum is not the largest element of its cycle in the inverse image under the fundamental bijection.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks.cycleFrom_B_record_block`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks.nonrecord_not_B_leader`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverse](ThetaBasicInverse.md)
