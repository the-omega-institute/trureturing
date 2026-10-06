# Coloring Hereditarily Sparse Graphs

## Abstract

Hereditary average degree at most three and exclusion of four-cliques suffice for a proper three-coloring.

FiniteSimpleGraphs means simple graphs on finite vertex types with decidable adjacency. For a finite vertex set S, InducedEdges(G,S) is the number of unordered edges of the induced simple graph. Parallel indexed owners are not counted here: an application from an indexed edge family must first bound its distinct simple edges by its indexed owners. CliqueFree(G,4) excludes four pairwise adjacent vertices, and Colorable(G,3) asserts a proper coloring with three colors.

**Theorem 1.1 (Hereditary Sparsity and Three Colors).**

$$\forall G \in \mathrm{FiniteSimpleGraphs},\; (\left(\forall S \in \mathrm{FiniteVertexSets}\left(G\right),\; 2 \cdot \mathrm{InducedEdges}\left(G, S\right) \leq 3 \cdot \mathrm{Card}\left(S\right)\right) \land \mathrm{CliqueFree}\left(G, 4\right)) \Rightarrow (\mathrm{Colorable}\left(G, 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Brooks/HereditaryColoring.hereditary_sparse_three_colorable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use strong induction over finite vertex sets. When an induced graph has a vertex with fewer than three neighbors, delete that vertex, apply the induction hypothesis, and reuse the low-degree extension lemma to restore it. Otherwise every degree is at least three. The handshake identity and the assumed edge bound force every degree to equal three. The induced graph inherits four-clique exclusion, so the transplanted Brooks theorem supplies its coloring.

The empty graph is included. A hereditary average degree bound allows vertices of degree greater than three before deletion. This graph theorem does not assert that independently colored arithmetic blocks have compatible residues or that their replacement labels satisfy a global covering budget.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Brooks/HereditaryColoring.hereditary_sparse_three_colorable`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/Subcubic](Subcubic.md)
