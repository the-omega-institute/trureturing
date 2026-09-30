# Deletion of the Least Value

## Abstract

Deleting the smallest doubled letter preserves avoidance and first order.

**Theorem 1.1 (Deleting both ones preserves avoidance).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion.delete_lowest_avoider`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion.delete_lowest_avoider` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Removing both copies of one and decrementing the remaining letters sends an avoider of size n plus one to an avoider of size n.

**Theorem 1.2 (First order survives filtering).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion.first_order_after_filter`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion.first_order_after_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Filtering a word above k preserves the order of first occurrences of any two retained letters.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion.delete_lowest_avoider`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion.first_order_after_filter`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum](NonnestingBasicSum.md)
