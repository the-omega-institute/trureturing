# Weighted and Parity-Restricted Divisor Sums

## Abstract

Weighted and parity-restricted alternating odd divisor sums satisfy explicit bounds.

**Theorem 1.1 (Sign and square bound for the weighted sum).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted.weighted_alternating_odd_divisor_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted.weighted_alternating_odd_divisor_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural number n, let W be the sum over i from zero through n of (-1) raised to n minus i, multiplied by n minus i plus one and by the number of positive divisors of 2i plus one. Then W multiplied by (-1) raised to n is nonnegative and is at most the square of the integer quotient of the natural square root of 2n plus three, increased by one, divided by two. A weighted character convolution and a hyperbola decomposition give both inequalities.

**Theorem 1.2 (Square-root bound for the parity-restricted sum).**

Lean statement: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted.parity_alternating_odd_divisor_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted.parity_alternating_odd_divisor_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George E. Andrews, Mohamed El Bachraoui (2025). *Certain positive q-series and inequalities for two-color partitions*. DOI: [10.48550/arXiv.2507.09276](https://doi.org/10.48550/arXiv.2507.09276). URL: <https://arxiv.org/abs/2507.09276v1>.

*Commentary.*

For every natural number n, sum over the integers i from zero through n having the same parity as n the number of positive divisors of 2i plus one, multiplied by (-1) raised to the integer quotient of n minus i divided by two. The absolute value of this sum is at most the natural square root of 2n plus one, increased by two. Characters modulo eight express the parity restriction as signed divisor convolutions.

## References

- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted.parity_alternating_odd_divisor_sum_bound`
- Truth anchor: `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted.weighted_alternating_odd_divisor_sum_bound`
- Dependency: [D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiCharacter](AndrewsElBachraouiCharacter.md)
