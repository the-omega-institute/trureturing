# Occurrence Orders in Doubled Words

## Abstract

The two occurrences of each letter govern nonnesting.

**Definition 1.1 (Position of the second occurrence).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.secondPos`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.secondPos` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Starting just after the first occurrence, this index searches for the next copy of the letter and adds the starting offset.

**Theorem 1.2 (Decomposition around two copies).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.count_two_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.count_two_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A letter occurring exactly twice separates a word into three pieces containing no further copy of that letter.

**Theorem 1.3 (Multiplicity in a doubled permutation).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.doubled_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.doubled_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Every letter in the doubled support occurs exactly twice.

**Theorem 1.4 (Reversed orders create nesting).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.nesting_of_reversal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.nesting_of_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

If the first occurrences of two distinct letters have one order and their second occurrences have the reverse order, the word contains 1221 or 2112.

**Theorem 1.5 (Nonnesting as matching occurrence orders).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.nonnesting_iff_equal_orders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.nonnesting_iff_equal_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For a word with exactly two copies of every letter, avoiding 1221 and 2112 is equivalent to first-occurrence order implying the same second-occurrence order.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.count_two_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.doubled_count`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.nesting_of_reversal`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.nonnesting_iff_equal_orders`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.secondPos`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingDefs](NonnestingDefs.md)
