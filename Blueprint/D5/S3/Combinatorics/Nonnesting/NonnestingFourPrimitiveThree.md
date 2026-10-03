# Three-Letter Order Restrictions

## Abstract

Forbidden patterns restrict the two occurrence orders of three distinct letters.

**Theorem 1.1 (A smallest letter cannot start last).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree.forbidden_last_first`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree.forbidden_last_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For three increasing letters with matching first and second orders, avoiding 2231 and 3221 excludes either ordering in which the smallest letter first appears after both others.

**Theorem 1.2 (Separation forced by the remaining patterns).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree.separated_three_orders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree.separated_three_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Avoiding 1231 and 1312 forces the second occurrence of the earliest relevant letter before a later first occurrence in each of three specified first-order arrangements.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree.forbidden_last_first`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveThree.separated_three_orders`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders](NonnestingBasicOrders.md)
