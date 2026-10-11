# Subcubic Brooks Theorem

## Abstract

Every finite simple graph with maximum degree at most three and no four-clique admits a proper three-coloring.

Juan Pablo Traverso Gianini's formalization proves the subcubic case of Brooks' theorem. The graph may be disconnected and its vertex type may be empty. FiniteSimpleGraphs below means a simple graph on a finite enumerated vertex type with decidable adjacency. MaxDegree is the maximum vertex degree; CliqueFree(G,4) excludes a set of four pairwise adjacent vertices. Colorable(G,3) means existence of a map from vertices to three colors that separates adjacent vertices.

**Theorem 1.1 (Three Colors for Subcubic Graphs).**

$$\forall G \in \mathrm{FiniteSimpleGraphs},\; (\mathrm{MaxDegree}\left(G\right) \leq 3 \land \mathrm{CliqueFree}\left(G, 4\right)) \Rightarrow (\mathrm{Colorable}\left(G, 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/Subcubic.brooks_cubic` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *BrooksSubcubic: finite subcubic four-clique-free graph coloring*. URL: <https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic>.

*Commentary.*

The proof colors each connected component. A component with a vertex of degree below three uses a greedy ordering. A cubic component uses the good-triple construction or a cut partition and compatible color gluing. The hereditary density application is proved separately; an average degree bound alone is not this theorem's hypothesis.

The cited source contains the formal proof; its helper lemmas organize the greedy ordering, separating vertices, endblocks and color gluing. Brooks' classical theorem supplies the mathematical precedent.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/Subcubic.brooks_cubic`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Coloring](Coloring.md)
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Cuts](Cuts.md)
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Endblock](Endblock.md)
