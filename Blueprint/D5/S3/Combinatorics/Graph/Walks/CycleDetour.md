# Cycle extension by a detour

## Abstract

A path outside a cycle and an edge between its terminal successors give a longer actual cycle.

**Theorem 1.1 (Exact support and length of the extended cycle).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall a \in V,\; \forall s \in V,\; \forall p \in \operatorname{Walk}\left(G, s, a\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall Q \in \operatorname{Walk}\left(G, a, \operatorname{getVert}\left(p, i\right)\right),\; \left(\operatorname{Adj}\left(G, a, s\right) \land \left(\operatorname{IsCycle}\left(\operatorname{cons}\left(\operatorname{edge}\left(a, s\right), p\right)\right) \land \left(i < \operatorname{length}\left(p\right) \land \left(\operatorname{IsPath}\left(Q\right) \land \left(2 \le \operatorname{length}\left(Q\right) \land \left(\operatorname{TerminalClean}\left(Q, \operatorname{cons}\left(\operatorname{edge}\left(a, s\right), p\right), a, \operatorname{getVert}\left(p, i\right)\right) \land \operatorname{Adj}\left(G, s, \operatorname{getVert}\left(p, i + 1\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists D \in \operatorname{Walk}\left(G, \operatorname{getVert}\left(p, i\right), \operatorname{getVert}\left(p, i\right)\right),\; \operatorname{IsCycle}\left(D\right) \land \left(\operatorname{length}\left(D\right) = \operatorname{length}\left(\operatorname{cons}\left(\operatorname{edge}\left(a, s\right), p\right)\right) + \operatorname{length}\left(Q\right) - 1 \land \operatorname{supportSet}\left(D\right) = \operatorname{union}\left(\operatorname{supportSet}\left(\operatorname{cons}\left(\operatorname{edge}\left(a, s\right), p\right)\right), \operatorname{supportSet}\left(Q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CycleDetour.exists_cycle_through_detour` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

Let G be a simple undirected graph on any type V. Let a be adjacent to s, and let p be an actual walk from s to a such that C, obtained by putting the edge a-to-s before p, is a cycle. Fix an index i strictly less than p.length. Let Q be a path from a to p.getVert(i), of length at least two, whose support meets C only at these two endpoints. Suppose s is adjacent to p.getVert(i+1). Then there is an actual cycle D based at p.getVert(i), of length C.length + Q.length - 1. Its support is exactly the union of the supports of C and Q.

No finiteness assumption on V or spanning assumption on C is needed. The index zero is permitted, as is the last index below p.length; consequently, consecutive terminal vertices and a nil residual cycle piece remain included.

Cut the detour at its first and last edges, retaining its nonempty interior path. Cut p just after its indexed terminal. Reverse the first residual cycle path, keep the second in its original direction, and place the detour interior last. The successor edge and the first and last detour edges connect these three pieces into a ring. The old cycle vertices occur exactly once, and every interior detour vertex occurs exactly once outside that cycle.

Induce each piece on the subtype defined by the union of these actual supports. Their support lists partition every vertex of that subtype with count one, and the list has length at least three. The path-ring splicing theorem gives a Hamiltonian cycle on this subtype. Mapping by the injective inclusion gives D in G; the support inventory yields its exact union and its length. Hamiltonicity here concerns the union subtype only.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CycleDetour.exists_cycle_through_detour`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/OrderedTwoCutSlicing](OrderedTwoCutSlicing.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PathRingSplicing](PathRingSplicing.md)
