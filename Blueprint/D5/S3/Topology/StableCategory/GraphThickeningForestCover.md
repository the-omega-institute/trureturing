# The ordinary categorical cover number of graph thickenings

## Abstract

The ordinary categorical cover number of graph thickenings

**Theorem 1.1 (The ordinary categorical cover number equals arboricity).**

Lean statement: `D5/S3/Topology/StableCategory/GraphThickeningForestCover.ordinary_cover_number_eq_arboricity`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/GraphThickeningForestCover.ordinary_cover_number_eq_arboricity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Each original vertex is a minimal singleton face. Each edge gives an added maximal triangle. On a cycle an upward comparison fixes all edge maxima and then all the singleton vertices by pairwise intersection. A downward comparison fixes the singletons and then the edge maxima. The cycle stays fixed throughout any order fence from the inclusion. Consequently a categorical lower set can contain only a forest among its edge labels. Conversely, within a forest piece replace each leaf by its unique edge midpoint, then replace that midpoint by the apex. Isolated vertices move directly to the apex. These comparison fences contract the forest pieces, giving exactly the forest covering number when the graph has an edge.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/GraphThickeningForestCover.ordinary_cover_number_eq_arboricity`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ForestPacking](../../Combinatorics/Graph/Walks/ForestPacking.md)
- Dependency: [D5/S3/Topology/StableCategory/GraphThickeningStableCover](GraphThickeningStableCover.md)
