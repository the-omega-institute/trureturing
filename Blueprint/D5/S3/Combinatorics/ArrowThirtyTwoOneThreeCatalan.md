# Catalan Orders of the Final Cycle

## Abstract

The final-cycle orders are counted by Catalan numbers through classical 132-avoidance.

**Definition 1.1 (Classical 132 occurrence).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.Has132`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.Has132` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A word contains 132 when entries at positions i less than j less than k have values at i less than the value at k, which is less than the value at j.

**Definition 1.2 (Adjacent 13-2 occurrence).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.HasAdj132`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.HasAdj132` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A word contains 13-2 when the first two entries of such a triple are adjacent, while the third occurs later.

**Theorem 1.3 (Adjacent and classical patterns coincide).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.hasAdj132_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.hasAdj132_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a word with distinct entries, a 13-2 occurrence exists exactly when a classical 132 occurrence exists.

**Theorem 1.4 (Avoidance across a maximum).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.avoids132_append_max_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.avoids132_append_max_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When m exceeds every entry of L and R, their concatenation around m avoids 132 exactly when both parts avoid 132 and every entry of L is at least every entry of R.

**Theorem 1.5 (Uniqueness of upper parts).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.upper_parts_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.upper_parts_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Two upper-closed subsets of the same finite ordered set are equal when they have the same cardinality.

**Theorem 1.6 (Upper parts of every size).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.exists_upper_part`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.exists_upper_part` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Every size from zero through the cardinality of a finite ordered set occurs as the cardinality of an upper-closed subset.

**Theorem 1.7 (Counting 132-avoiding orders).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.ncard_avoid132`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.ncard_avoid132` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The number of 132-avoiding orders of any finite set of natural numbers is the Catalan number indexed by its cardinality.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.Has132`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.HasAdj132`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.avoids132_append_max_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.exists_upper_part`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.hasAdj132_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.ncard_avoid132`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.upper_parts_unique`
