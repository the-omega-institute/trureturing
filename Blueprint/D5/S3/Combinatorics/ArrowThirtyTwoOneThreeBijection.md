# Reconstructing the Final Cycle

## Abstract

The prefix and final cycle of an avoider satisfy complementary edge and pattern conditions.

**Theorem 1.1 (Prefix successors before the final cycle).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.hat_append_final_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.hat_append_final_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If m exceeds every entry of q, placing m and a following word after q leaves every inverse Foata successor of an entry of q unchanged.

**Theorem 1.2 (No prefix edge crosses a final-cycle letter).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.no_prefix_edge_crosses_final_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.no_prefix_edge_crosses_final_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For an avoider split before its largest value, a final-cycle letter c above a prefix letter a cannot lie below the inverse Foata successor of a in the prefix.

**Theorem 1.3 (The prefix inherits the edge condition).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.prefix_edge_condition_of_avoider`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.prefix_edge_condition_of_avoider` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Every ascending inverse Foata edge in the prefix of an avoider has all intermediate values before its endpoint within that prefix.

**Theorem 1.4 (Edges of a permissible final cycle).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.final_cycle_edge_condition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.final_cycle_edge_condition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Suppose the whole word is a permutation, the final-cycle word ends in its largest letter b, and it avoids 132. Then each edge starting in that word satisfies the avoidance edge condition.

**Theorem 1.5 (Appending a largest letter preserves 132).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.has132_append_max_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.has132_append_max_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If b exceeds every entry of u, the word u followed by b contains 132 exactly when u does.

**Theorem 1.6 (Necessary final-cycle conditions).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.final_cycle_strict_max_and_avoid132`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.final_cycle_strict_max_and_avoid132` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

In an avoider whose last cycle is n plus one followed by u and b, b strictly exceeds every letter of u, and u avoids 132.

**Theorem 1.7 (Counting singleton final cycles).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.singleton_final_cycle_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.singleton_final_cycle_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The avoiders of size n plus one ending in n plus one are counted by the avoidance number at n.

**Theorem 1.8 (Constructing an avoider).**

Lean statement: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.construct_avoider_of_local_conditions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.construct_avoider_of_local_conditions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A permutation formed from a prefix q and final cycle beginning with n plus one is an avoider when prefix edges are closed, no prefix edge crosses a final-cycle letter, and the final-cycle word ends in its largest letter after a 132-avoiding initial part.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.construct_avoider_of_local_conditions`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.final_cycle_edge_condition`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.final_cycle_strict_max_and_avoid132`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.has132_append_max_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.hat_append_final_cycle`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.no_prefix_edge_crosses_final_cycle`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.prefix_edge_condition_of_avoider`
- Truth anchor: `D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.singleton_final_cycle_count`
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp](ArrowThirtyTwoOneThreeDecomp.md)
- Dependency: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs](ArrowThirtyTwoOneThreeDefs.md)
