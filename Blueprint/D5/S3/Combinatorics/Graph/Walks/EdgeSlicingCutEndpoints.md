# Actual Endpoints of Hamilton Cycle Slices

## Abstract

Cutting actual selected Hamilton cycle edges preserves the actual cut-vertex endpoints of every remaining path.

**Theorem 1.1 (Every Slice Ends at Actual Selected Edges).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall E \in \mathrm{Finset}\left(\mathrm{Sym2}\left(V\right)\right),\; \forall a \in V,\; \forall p \in \mathrm{Walk}\left(G, a, a\right),\; ((\mathrm{IsHamiltonianCycle}\left(p\right)) \land ((\mathrm{Nonempty}\left(E\right)) \land (\forall e \in \mathrm{Sym2}\left(V\right),\; (e \in E) \Rightarrow (e \in \mathrm{edgeSet}\left(p\right))))) \Rightarrow (\exists L \in \mathrm{List}\left(\mathrm{Piece}\left(G\right)\right),\; (\forall z \in \mathrm{Piece}\left(G\right),\; (z \in L) \Rightarrow (\mathrm{IsPath}\left(\mathrm{walk}\left(z\right)\right))) \land ((\forall v \in V,\; \mathrm{count}\left(v, \mathrm{flatMapSupport}\left(L\right)\right) = 1) \land ((\forall e \in \mathrm{Sym2}\left(V\right),\; (e \in \mathrm{flatMapEdges}\left(L\right)) \Leftrightarrow ((e \in \mathrm{edgeSet}\left(p\right)) \land (\mathrm{Not}\left(e \in E\right)))) \land ((\mathrm{length}\left(L\right) = \mathrm{card}\left(E\right)) \land (\forall z \in \mathrm{Piece}\left(G\right),\; (z \in L) \Rightarrow ((\exists f \in \mathrm{Sym2}\left(V\right),\; (f \in E) \land (\mathrm{start}\left(z\right) \in f)) \land (\exists f \in \mathrm{Sym2}\left(V\right),\; (f \in E) \land (\mathrm{finish}\left(z\right) \in f))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/EdgeSlicingCutEndpoints.exists_cycle_edge_slicing_with_cut_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a simple graph on a finite type V with decidable equality, p an actual Hamilton cycle, and E a nonempty finite set of actual edges of p. The theorem constructs exactly |E| simple path pieces. Their combined supports contain each vertex exactly once, and their combined edge list contains precisely the actual cycle edges outside E. In addition, the start and finish of every piece are incident to edges of E. Adjacent cuts retain their common vertex as a nil piece.

Open the original cycle at a selected actual edge using the frozen endpoint-aware opening theorem. Induction over the remaining actual path proves that its first piece can end only at the original finish or at a selected cut, and every later piece starts at a selected cut and has the same finish alternative. The two original endpoints belong to the opening cut. Combining these boundary laws with the existing literal support, edge and length laws yields the endpoint certificate without changing the retained vertex or edge inventory.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/EdgeSlicingCutEndpoints.exists_cycle_edge_slicing_with_cut_endpoints`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
