# The Final-Cycle Bijection

## Abstract

Gap data and a Catalan order reconstruct an avoider with a prescribed final-cycle length.

**Definition 1.1 (Final-cycle strata).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.Stratum`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.Stratum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The stratum at n and k consists of avoiders on 1 through n plus one with exactly k letters after the largest value.

**Definition 1.2 (Admissible selected-letter orders).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.CycleOrders`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.CycleOrders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

An admissible order permutes a chosen list, ends in a largest letter of that list, and avoids 132.

**Definition 1.3 (Joining the last cycle).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.joinLastCycle`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.joinLastCycle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Place n plus one between the closed-edge prefix of a gap datum and an admissible order of its selected letters. The resulting avoider lies in the stratum with that final-cycle length.

**Theorem 1.4 (Unique final-cycle decomposition).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.joinLastCycle_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.joinLastCycle_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For every n and k, joining gap data with admissible orders is a bijection onto avoiders with k plus one letters after their largest value.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.CycleOrders`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.Stratum`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.joinLastCycle`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeLastCycle.joinLastCycle_bijective`
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode](ArrowThirtyTwoOneThreeGapCode.md)
