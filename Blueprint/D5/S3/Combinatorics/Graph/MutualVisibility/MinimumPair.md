# MinimumPair

## Abstract

Minimum rooted pairs and the full mixed mutual-visibility separator equality.

**Theorem 1.1 (Full maximal connectivity).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair.result` (`✓ std3`). ∎

*Resolves.* `Problems/fresan-figueroa-goldfeder-lozano-2026-mutual-visibility-maximal-connectivity` (proved) by `D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fresan-figueroa-goldfeder-lozano-2026-mutual-visibility-maximal-connectivity","declaration_gid":"D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

For every finite nonempty connected simple undirected host, the graph of all mutually visible configurations has vertex connectivity equal to minimum degree. Visibility uses an existential shortest path in the original host for each selected pair. Configurations include the empty set and every feasible rank. Moves include token addition and removal and every slide along an actual host edge to an unoccupied label. Hosts of orders one and two are included. Vertex connectivity uses deletion to at most one vertex or failure of preconnectedness, so a complete graph on q vertices has connectivity q minus one.

Fix an arbitrary configuration cut smaller than minimum degree. The empty configuration bounds minimum degree by host order, so there is a clean root and all surviving singletons lie in one component. If another surviving component had no pair, the high-rank component theorem would give a configuration of degree at most the cut size. Thus a component stranded from the root contains a distinct pair, and both endpoint singletons are cut. Choose a pair minimizing the sum of root distances and orient it by rooted comparability.

For each outside label, the pair has at most two slide neighbors, one for each actual host edge to an endpoint, and at most one addition. If the outside singleton is cut, it supplies one local payment. A visible triple supplies either its own cut or a cut pair face: all three faces cannot belong to the stranded component because three pairwise rooted comparabilities contradict visibility. For a nonvisible triple with two slides, the common neighbor lies strictly closer to the root than the farther endpoint; minimality forces the closer replacement pair into the cut.

If the outside singleton survives, every slide endpoint is cut. A surviving visible addition has both other pair faces cut. All cases are paid within the local class, except that a surviving visible triple with two actual slides can require one more cut. With one fixed inward predecessor of the oriented pair, the simultaneous inward-payment theorem supplies these extra cuts injectively. Each extra payment has exactly two labels outside the base pair, so it is disjoint from all local classes and from the internal class. The joint budget therefore bounds the full pair degree by the same cut size.

This contradicts the cut size below minimum degree. Hence every surviving configuration reaches the root singleton after every such cut. The resulting preconnectedness and the generic separator inequalities give equality. No assumption on girth, diameter, global star forests, sparse slides, minimum separators, or the ranks of other configurations is used.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair.result`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability](RootComparability.md)
