# Splitting at the Largest Value

## Abstract

The largest value begins the final cycle, whose entries have a constrained order.

**Theorem 1.1 (Appending a new maximum).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_append_fresh_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_append_fresh_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If m exceeds every entry of q, appending m leaves the inverse Foata successor of each entry of q unchanged.

**Theorem 1.2 (The last edge returns to the maximum).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_last_entry_eq_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_last_entry_eq_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

In a permutation of 1 through n plus one, the inverse Foata successor of its last entry is n plus one.

**Theorem 1.3 (Successors after the maximum).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_next_after_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_next_after_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For any entry after n plus one that has a following entry, the inverse Foata successor is that following entry.

**Theorem 1.4 (A singleton final cycle).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.append_max_avoiders_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.append_max_avoiders_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Appending the new maximum n plus one to q produces an avoider exactly when q is an avoider on 1 through n.

**Theorem 1.5 (The last letter is largest).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.final_cycle_last_is_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.final_cycle_last_is_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If an avoider ends in a final cycle beginning with n plus one and ending in a, every preceding letter of that cycle is at most a.

**Theorem 1.6 (The final-cycle tail avoids 132).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.final_cycle_avoid132`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.final_cycle_avoid132` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The word following the largest value in the final cycle of an avoider contains no classical 132 pattern.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.append_max_avoiders_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.final_cycle_avoid132`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.final_cycle_last_is_max`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_append_fresh_max`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_last_entry_eq_max`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.hat_next_after_max`
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan](ArrowThirtyTwoOneThreeCatalan.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfCharacterization](ArrowWilfCharacterization.md)
