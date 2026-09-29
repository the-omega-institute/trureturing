# Value Gaps and Closed Edges

## Abstract

The edge condition respects increasing relabelling and cuts at missing values.

**Definition 1.1 (Closed ascending edges).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.ClosedEdges`

*Formalization.* `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.ClosedEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A word has closed edges when every value strictly between an entry and a larger inverse Foata successor appears before that successor in the word.

**Theorem 1.2 (Increasing relabelling of successors).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.hat_map_strictMono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.hat_map_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For an entry belonging to a word, a strictly increasing relabelling carries its inverse Foata successor to the successor of its relabelled entry.

**Theorem 1.3 (Translation of closed edges).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_translate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Adding the same nonnegative integer to every letter preserves and reflects the closed-edge condition.

**Theorem 1.4 (Successors in ordered concatenations).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.hat_append_ordered`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.hat_append_ordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When every letter of L is smaller than every letter of R, the inverse Foata successor of each letter in L or R agrees with its successor within that part.

**Theorem 1.5 (Closed edges in ordered concatenations).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_append_ordered`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_append_ordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When all letters of L are below all letters of R, their concatenation has closed edges exactly when each part has closed edges.

**Theorem 1.6 (Cutting at a missing value).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_value_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_value_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A word with distinct letters and closed edges, omitting c, consists first of all its letters below c and then all its letters above c.

**Theorem 1.7 (Cycles cannot cross a missing value).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_cycle_confinement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_cycle_confinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

In a word with distinct letters and closed edges that omits c, every iterate of the inverse Foata successor of an entry remains in the word and stays on the same side of c as that entry.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.ClosedEdges`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_append_ordered`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_cycle_confinement`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_translate`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_value_cut`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.hat_append_ordered`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.hat_map_strictMono`
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection](ArrowThirtyTwoOneThreeBijection.md)
