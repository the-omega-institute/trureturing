# GeneratingFibers

## Abstract

The nonabelian square-root deficit.

**Definition 1.1 (All generating ordered pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.generatingPairs`

*Formalization.* `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.generatingPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

For a subgroup H of an arbitrary finite group G, generatingPairs H contains exactly every ordered pair (a,b) whose subgroup closure is H, including repeated entries and identities.

**Definition 1.2 (The actual fiber cardinality).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount`

*Formalization.* `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

The natural number r_H is the cardinality of generatingPairs H.

**Theorem 1.3 (The identity fiber).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_bot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

For every finite group, r_bottom=1. Its unique pair is (1,1).

**Theorem 1.4 (Every other realized fiber has at least three pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_ge_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_ge_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

If H is not the trivial subgroup and r_H is positive, then r_H is at least three. A nonidentity generator supplies distinct ordered pairs; when both entries are nonidentity and distinct, the six-pair construction applies.

**Theorem 1.5 (A six-pair fiber from noncommutativity).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.exists_large_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.exists_large_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

For every finite group with a noncommuting pair, some subgroup H has r_H at least six. If a and b do not commute, then a, b and ab are pairwise distinct and a,b are nonidentity. The six distinct pairs (a,b), (b,a), (a,ab), (ab,a), (b,ab), (ab,b) generate the same subgroup. The closure equalities use multiplication and inversion in that subgroup.

**Theorem 1.6 (The complete fiber partition).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.sum_pairCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.sum_pairCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

Summing r_H over all subgroups gives card(G)^2, by partitioning every ordered pair according to its generated subgroup. Subgroups with zero fibers remain in the index type.

**Theorem 1.7 (Prime-order fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

If the actual subgroup H has prime order p, then r_H=p^2-1. Every pair in H other than (1,1) generates H, using the prime-cardinality subgroup dichotomy. The proof constructs an injective correspondence with these pairs; no fiber count is assumed.

**Theorem 1.8 (An actual Cauchy subgroup).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.exists_prime_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.exists_prime_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

For every finite group of order greater than one, Cauchys theorem supplies a prime p and an actual subgroup H of cardinality p with r_H=p^2-1.

**Definition 1.9 (The realized subgroup set).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.positiveFibers`

*Formalization.* `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.positiveFibers` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

The finite set consists exactly of the subgroups H with positive r_H. This set is used only to count realized fibers, and does not remove isolated subgroup vertices from the graph.

**Theorem 1.10 (The nonabelian square-root deficit).**

Lean statement: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.sqrt_sum_le_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.sqrt_sum_le_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2026). *Various spectra and energies of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2601.04004](https://doi.org/10.48550/arXiv.2601.04004). URL: <https://arxiv.org/abs/2601.04004v1>.

*Commentary.*

Let M=card(G)^2 and t be the number of positive fibers. For every finite nonabelian G, the sum of sqrt(r_H) over all subgroups is at most M-t. The trivial fiber r=1 costs one unit relative to sqrt(r)<=r-1. Every other positive fiber has r>=3 and satisfies that inequality; a six-pair fiber satisfies sqrt(r)<=r-2 and supplies the missing unit. Summing this pointwise bound cancels both corrections. This estimate concerns fibers realized by one actual group.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.exists_large_fiber`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.exists_prime_fiber`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.generatingPairs`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_bot`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_ge_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.pairCount_prime`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.positiveFibers`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.sqrt_sum_le_deficit`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/GeneratingFibers.sum_pairCount`
- Dependency: [D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation](CyclicExtensionRefutation.md)
