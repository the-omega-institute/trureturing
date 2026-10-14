# Cutting Actual Graph Walks into Paths

## Abstract

Deleting a nonempty collection of actual Hamilton cycle edges yields exactly one path per deleted edge, with every vertex occurring once.

Let G be a simple graph on a type V with decidable equality. A Piece(G) records two endpoints and an actual G-walk between them. For a list L of pieces, flatMapSupport(L) concatenates their full vertex-support lists, and flatMapEdges(L) concatenates their undirected edge lists. Edges have type Sym2(V), so their orientation is forgotten. The operator filterIn retains the list occurrences belonging to a finite edge set E; filterOut retains the occurrences outside E.

**Theorem 1.1 (Literal Support and Edge Lists after Cutting a Path).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall E \in \mathrm{Finset}\left(\mathrm{Sym2}\left(V\right)\right),\; \forall start \in V,\; \forall finish \in V,\; \forall p \in \mathrm{Walk}\left(G, start, finish\right),\; (\mathrm{IsPath}\left(p\right)) \Rightarrow (\exists L \in \mathrm{List}\left(\mathrm{Piece}\left(G\right)\right),\; (\forall z \in \mathrm{Piece}\left(G\right),\; (z \in L) \Rightarrow (\mathrm{IsPath}\left(\mathrm{walk}\left(z\right)\right))) \land ((\mathrm{flatMapSupport}\left(L\right) = \mathrm{support}\left(p\right)) \land ((\mathrm{flatMapEdges}\left(L\right) = \mathrm{filterOut}\left(E, \mathrm{edges}\left(p\right)\right)) \land (\mathrm{length}\left(L\right) = \mathrm{length}\left(\mathrm{filterIn}\left(E, \mathrm{edges}\left(p\right)\right)\right) + 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/EdgeSlicing.exists_path_edge_slicing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any path p and finite set E of undirected edges admit a list of actual path pieces. Their concatenated supports equal p's support in its original order. Their concatenated edges equal p's edge list with every selected occurrence removed. There is one more piece than selected edge occurrences. Edges of E that never occur in p cause no cut.

The construction follows the actual walk from its first edge. A selected next edge ends the current piece and starts the next piece at its other endpoint. An unselected edge extends the current piece. Consecutive cuts therefore keep a nil walk at their common vertex; this piece has one vertex and no edges. Induction on the walk proves the support, edge-list and length identities, while the original path condition ensures every piece is a path.

**Theorem 1.2 (Open an Actual Hamilton Cycle at Its Supplied Edge).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall a \in V,\; \forall x \in V,\; \forall y \in V,\; \forall p \in \mathrm{Walk}\left(G, a, a\right),\; ((\mathrm{IsHamiltonianCycle}\left(p\right)) \land (\mathrm{Sym2}\left(x, y\right) \in \mathrm{edgeSet}\left(p\right))) \Rightarrow (\exists q \in \mathrm{Walk}\left(G, y, x\right),\; (\mathrm{IsHamiltonian}\left(q\right)) \land (\forall e \in \mathrm{Sym2}\left(V\right),\; (e \in \mathrm{edges}\left(q\right)) \Leftrightarrow ((e \in \mathrm{edges}\left(p\right)) \land (\neg e = \mathrm{Sym2}\left(x, y\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/EdgeSlicing.exists_open_cycle_at_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A genuine undirected edge {x,y} of a Hamilton cycle can be removed to produce an actual Hamilton path from y to x. Its undirected edges are exactly the original cycle edges except {x,y}. Rotation and, when necessary, reversal of the supplied cycle earn the endpoint orientation; no new path is assumed. Keeping both endpoints in the walk type allows later actual seam splicing.

**Theorem 1.3 (Exactly One Actual Path per Selected Hamilton Cycle Edge).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall E \in \mathrm{Finset}\left(\mathrm{Sym2}\left(V\right)\right),\; \forall a \in V,\; \forall p \in \mathrm{Walk}\left(G, a, a\right),\; ((\mathrm{IsHamiltonianCycle}\left(p\right)) \land ((\mathrm{Nonempty}\left(E\right)) \land (\forall e \in \mathrm{Sym2}\left(V\right),\; (e \in E) \Rightarrow (e \in \mathrm{edgeSet}\left(p\right))))) \Rightarrow (\exists L \in \mathrm{List}\left(\mathrm{Piece}\left(G\right)\right),\; (\forall z \in \mathrm{Piece}\left(G\right),\; (z \in L) \Rightarrow (\mathrm{IsPath}\left(\mathrm{walk}\left(z\right)\right))) \land ((\forall v \in V,\; \mathrm{count}\left(v, \mathrm{flatMapSupport}\left(L\right)\right) = 1) \land ((\forall e \in \mathrm{Sym2}\left(V\right),\; (e \in \mathrm{flatMapEdges}\left(L\right)) \Leftrightarrow ((e \in \mathrm{edgeSet}\left(p\right)) \land (\mathrm{Not}\left(e \in E\right)))) \land (\mathrm{length}\left(L\right) = \mathrm{card}\left(E\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/EdgeSlicing.exists_cycle_edge_slicing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume V is finite, p is an actual Hamilton cycle, and E is a nonempty finite set whose edges all belong to p's edge set. Then exactly |E| actual path pieces remain. Across their full supports, every vertex occurs exactly once. An undirected edge occurs among their edges exactly when it belongs to the original cycle and is outside E. Adjacent selected edges are allowed.

Choose an edge of E and rotate the actual cycle to one of its endpoints. At that endpoint the chosen edge leads either to the second vertex or to the penultimate vertex; reversing the cycle handles the second case. Removing the first edge opens the cycle into a Hamilton path whose edges are exactly the original cycle edges except that chosen edge. Cutting this path removes the remaining selected edges. Its edge list has no repetitions, so the number of remaining selected occurrences is |E|-1. The path construction then gives |E| pieces and preserves every vertex once.

These results concern a supplied actual path or Hamilton cycle and actual selected edges. For prefix-reversal constructions, one must additionally prove that the chosen native generator edges belong to that cycle and establish the endpoint orientations needed to join the resulting pieces.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/EdgeSlicing.exists_cycle_edge_slicing`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/EdgeSlicing.exists_open_cycle_at_edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/EdgeSlicing.exists_path_edge_slicing`
