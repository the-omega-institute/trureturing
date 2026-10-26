# Divisor and Gauss-Product Bounds

## Abstract

Odd divisor pairing and triangular coefficient counting give the required bounds.

**Theorem 1.1 (Odd divisor cardinality bound).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.odd_divisors_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.odd_divisors_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural number M that is odd, the cardinality of its divisor set is at most the natural square root of M plus one.

**Theorem 1.2 (Parity-compatible square-root row count).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.gauss_pair_count_le_sqrt_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.gauss_pair_count_le_sqrt_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural n and finite set s of ordered natural pairs, if every member has triangular sum at most n and the required parity, the real cardinality of s is at most the sum of its square-root row majorants. This is the same row injection used by the Gauss coefficient bound.

**Theorem 1.3 (Gauss-product coefficient bound).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.gauss_product_coefficient_count_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.gauss_product_coefficient_count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural number n, the coefficient of degree n in the finite Gauss product equals the cardinality of the parity-compatible triangular pairs. When n is at least 5, its real value is at most 97 divided by 120 times n, plus 27 divided by 32 times the square root of 2n plus one half, plus 13 divided by 25.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.gauss_pair_count_le_sqrt_sum`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.gauss_product_coefficient_count_bound`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds.odd_divisors_card_le`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq207TripleProduct](../InversionSeq/InversionSeq207TripleProduct.md)
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs](AndrewsElBachraouiDefs.md)
