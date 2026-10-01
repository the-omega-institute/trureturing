# Record-Block Characterization of 132-Avoidance

## Abstract

Consecutive record values and the ordering of record-block tails characterize 132-avoidance.

**Theorem 1.1 (Consecutive record values).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.adjacent_record_values`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.adjacent_record_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Two consecutive left-to-right maxima of a 132-avoiding permutation differ in value by exactly one.

**Theorem 1.2 (Earlier letters dominate a later block tail).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.earlier_entry_gt_later_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.earlier_entry_gt_later_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

In a 132-avoiding permutation, an entry before a record position exceeds every later entry in that record block.

**Theorem 1.3 (The record-block criterion).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.avoids132_iff_record_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.avoids132_iff_record_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

A permutation avoids 132 exactly when consecutive record values differ by one, each tail after a record and before the next record avoids 132 internally, and every earlier entry exceeds every entry in a later record-block tail.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.adjacent_record_values`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.avoids132_iff_record_blocks`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.earlier_entry_gt_later_tail`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverse](ThetaBasicInverse.md)
