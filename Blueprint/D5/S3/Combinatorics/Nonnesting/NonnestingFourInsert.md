# Insertion into Increasing-Order Avoiders

## Abstract

Two initial arrangements preserve four-pattern avoidance and first order.

**Theorem 1.1 (Crossing insertion preserves avoidance).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.crossing_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.crossing_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

If a word begins with one and avoids the four patterns, prepending 121 after shifting its tail yields an avoider of size one greater.

**Theorem 1.2 (First order after crossing insertion).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.crossing_insert_first_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.crossing_insert_first_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The 121 insertion preserves increasing order of first occurrences.

**Theorem 1.3 (First order after cut insertion).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.cut_insert_first_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.cut_insert_first_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Prepending 11 to a shifted word preserves increasing order of first occurrences.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.crossing_insert`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.crossing_insert_first_order`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.cut_insert_first_order`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum](NonnestingBasicSum.md)
