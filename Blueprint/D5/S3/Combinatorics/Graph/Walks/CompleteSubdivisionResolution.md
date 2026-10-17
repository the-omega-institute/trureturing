# Once-subdivided complete graphs have no edge multiset resolving set

## Abstract

Once-subdivided complete graphs have no edge multiset resolving set

Problem 24 of the cited versioned source, printed page 27, asks whether the edge multiset dimension of the once-subdivision of K_n is infinite for every n at least 3. Normalize a hypothetical resolving selection matrix by full complement and row rank. For n=2m use incidences e(m-1,m+1), e(m,m-1); for n=2m+1 use e(m,m+1), e(m+1,m-1). Their four counts agree. The odd case includes n=3. Rank renaming is a proved permutation; every edge and distance remains in the actual graph. The final theorem quantifies arbitrary sets of the entire vertex type and expands the minimum-endpoint distance multisets. Infinity is represented in extended naturals, with the empty family of resolving sets having infimum top. Elementary counting, matrix symmetry, finite permutations and complement identities are classical ingredients; no priority claim is made.

**Theorem 1.1 (no resolving set).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.no_resolving_set`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.no_resolving_set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

For every n at least three, every finite landmark subset of the full graph vertex set fails to resolve its actual edges.

**Theorem 1.2 (actual edge collision).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.actual_edge_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.actual_edge_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

For every such landmark subset there are two distinct actual unordered graph edges with equal minimum-shortest-endpoint distance multisets.

**Definition 1.3 (edgeMultisetDimension).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.edgeMultisetDimension`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.edgeMultisetDimension` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The edge multiset dimension is the extended-natural infimum of cardinalities of resolving landmark sets. If no such set exists the infimum is infinity.

**Theorem 1.4 (edgeMultisetDimension eq top).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.edgeMultisetDimension_eq_top`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.edgeMultisetDimension_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

For every n at least three the edge multiset dimension is infinity.

**Theorem 1.5 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.result` (`✓ std3`). ∎

*Resolves.* `Problems/farhan-2026-complete-subdivision-edge-multiset` (proved) by `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"farhan-2026-complete-subdivision-edge-multiset","declaration_gid":"D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

For every n at least three and every arbitrary set of full graph vertices, two distinct actual edges have equal multisets of the displayed minimum actual shortest endpoint distances, and the edge multiset dimension is infinity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.actual_edge_collision`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.edgeMultisetDimension`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.edgeMultisetDimension_eq_top`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.no_resolving_set`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution.result`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement](CompleteSubdivisionComplement.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionDegreeCollision](CompleteSubdivisionDegreeCollision.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix](CompleteSubdivisionMatrix.md)
