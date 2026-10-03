# Positional Constraints in Record Blocks

## Abstract

Simultaneous 132-avoidance of a permutation and its inverse constrains the positions of one and the maximum.

**Theorem 1.1 (The increasing suffix after one).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.suffix_after_one_increasing`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.suffix_after_one_increasing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

In a 132-avoiding permutation, the entries after an occurrence of one increase with position.

**Theorem 1.2 (One at the end of the final block).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.final_block_predecessor_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.final_block_predecessor_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

If a permutation and its inverse fundamental image both avoid 132 and its maximum occurs at a position strictly above zero and at least two places before the end, then the permutation ends with one.

**Theorem 1.3 (One after an initial maximum).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.one_block_second_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.one_block_second_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

If a permutation of size at least three and its inverse fundamental image both avoid 132, the permutation starts with its maximum and ends with a value greater than one, then its second entry is one.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.final_block_predecessor_one`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.one_block_second_one`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks.suffix_after_one_increasing`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral](ThetaBasicInverseGeneral.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords](ThetaIterateRecords.md)
