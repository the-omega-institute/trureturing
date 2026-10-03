# Refined Counts by Final Cycle

## Abstract

The final-cycle bijection yields a Catalan-weighted recurrence for the avoidance numbers.

**Theorem 1.1 (Catalan orders ending at the maximum).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.final_cycle_word_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.final_cycle_word_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a finite set t below b, the orders of t together with b that end in b and avoid 132 are counted by the Catalan number of the size of t.

**Theorem 1.2 (A positive final-cycle stratum).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.stratum_card_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.stratum_card_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For k plus one at most n, the number of avoiders of size n plus one with k plus one letters after n plus one is the kth Catalan number times the coefficient of x to the n minus k minus one in the (k plus two)nd power of the avoidance series.

**Theorem 1.3 (Recurrence for all avoidance numbers).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.count_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.count_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For every positive n, the count at n equals the count at n minus one plus the sum over k from one through n minus one of the (k minus one)st Catalan number times the coefficient of x to the n minus one minus k in the (k plus one)st power of the avoidance series.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.count_recurrence`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.final_cycle_word_count`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.stratum_card_positive`
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection](ArrowThirtyTwoOneThreeBijection.md)
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle](ArrowThirtyTwoOneThreeLastCycle.md)
