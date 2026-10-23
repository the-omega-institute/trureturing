# Cubic graphs are additively rigid

## Abstract

Every finite simple cubic graph has an AR-labeling onto the entire interval from one to its edge count.

**Definition 1.1 (The exact cubic graph assertion).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.claim`

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type and every simple graph of degree three at each vertex, there is a bijection from its edges onto the integers from one to its edge count such that every subset of the edges incident to any vertex has a distinct label sum. The assertion includes disconnected graphs and the graph with no vertices.

**Theorem 1.2 (Every cubic graph has an AR-labeling).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.result` (`✓ std3`). ∎

*Resolves.* `Problems/manattu-lakshmanan-2025-cubic-ar-graphs` (proved) by `D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"manattu-lakshmanan-2025-cubic-ar-graphs","declaration_gid":"D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For three positive distinct labels, the only possible subset-sum collision is that the two smaller labels sum to the largest. Four-vertex cubic graphs are complete; six-vertex cubic graphs are complete bipartite graphs or triangular prisms. Explicit labelings of these graphs transfer along graph isomorphisms. For at least twelve edges, fix two intersecting edges to labels one and two. The sum of the cardinalities of the bad vertex events is strictly less than the factorial size of the remaining bijection space, so one labeling has no bad vertex. The degree-sum formula excludes other positive orders below eight, and the empty graph has the empty edge labeling.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.claim`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.result`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs](CubicARGraphDefs.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLarge](CubicARGraphLarge.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso](CubicARGraphSmallIso.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphTransport](CubicARGraphTransport.md)
