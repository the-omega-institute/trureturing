# Alternating Odd Divisor Sums

## Abstract

A character modulo four and a hyperbola decomposition bound the alternating odd divisor sum.

**Theorem 1.1 (Square-root bound for the alternating divisor sum).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiCharacter.alternating_odd_divisor_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiCharacter.alternating_odd_divisor_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural number n, the absolute value of the sum over i from zero through n of (-1) raised to n minus i, multiplied by the number of positive divisors of 2i plus one, is at most the integer quotient of the natural square root of 2n plus one, increased by one, divided by two. The character modulo four expresses the sum as a signed divisor convolution. Splitting the divisor pairs at the square root gives the bound.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiCharacter.alternating_odd_divisor_sum_bound`
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiBounds](AndrewsElBachraouiBounds.md)
