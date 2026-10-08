# Prescribed-word realization

## Abstract

An essential directed multigraph realizes every prescribed positive legal word as one actual bi-infinite history, retaining every edge label.

**Theorem 1.1 (One actual history containing the entire prescribed word).**

$$\forall V \in Type, E \in Type, finiteVertices \in \operatorname{Fintype}\left(V\right), finiteEdges \in \operatorname{Fintype}\left(E\right), vertexEquality \in \operatorname{DecidableEq}\left(V\right), G \in \operatorname{DirectedMultigraph}\left(V, E\right), essential \in \operatorname{Essential}\left(G\right), n \in Nat, word \in \operatorname{LegalWord}\left(G, n\right), positive \in 0 < n,\; \exists x \in \operatorname{History}\left(G\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{historyEdge}\left(x, j\right) = \operatorname{wordEdge}\left(word, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/EssentialWordRealization.exists_history_containing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Essential means that each vertex has an actual outgoing edge and an actual incoming edge. Edges are elements of the supplied edge type, so loops and distinct parallel edges remain distinct. LegalWord stores all those edges and each target/source adjacency equation. History is the subtype of Int-indexed actual edges satisfying every adjacency equation.

In the display, historyEdge(x,j) is x evaluated at the integer cast of j; wordEdge(word,j) is the j-th prescribed edge. The history uses iterated incoming choices at negative times, the entire prescribed word at times 0 through n minus 1, and iterated outgoing choices afterward. The proof verifies both outer seams and every interior seam. No strong connectivity, word-extension assumption or redefinition by globally realizable words is present.

The positive-length requirement suffices for theorem 23.1: both table lengths, both seam lengths and the common recovery length are positive for all four natural radii, including zero. The empty LegalWord type is not asserted to model a zero-edge path with a specified vertex.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/EssentialWordRealization.exists_history_containing`
