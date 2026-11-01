# Bipartite linear-forest completion

## Abstract

Every finite bipartite linear forest with a strictly larger B part admits a color-preserving supergraph on the same full vertex type, still a linear forest, in which every A vertex has degree two.

**Theorem 1.1 (Saturation on the full original carrier).**

$$\forall alpha \in \mathrm{Type},\; \left(\operatorname{Fintype}\left(alpha\right) \land \operatorname{DecidableEq}\left(alpha\right)\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(alpha\right),\; \forall A \in \operatorname{Finset}\left(alpha\right),\; \forall B \in \operatorname{Finset}\left(alpha\right),\; \left(\operatorname{IsIndepSet}\left(G, A\right) \land \left(\operatorname{IsIndepSet}\left(G, B\right) \land \left(\operatorname{Disjoint}\left(A, B\right) \land \left(\operatorname{union}\left(A, B\right) = \operatorname{univ}\left(alpha\right) \land \left(\operatorname{IsAcyclic}\left(G\right) \land \left(\left(\forall x \in alpha,\; \operatorname{degree}\left(G, x\right) \le 2\right) \land \operatorname{card}\left(A\right) < \operatorname{card}\left(B\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists H \in \operatorname{SimpleGraph}\left(alpha\right),\; G \le H \land \left(\operatorname{IsAcyclic}\left(H\right) \land \left(\left(\forall x \in alpha,\; \operatorname{degree}\left(H, x\right) \le 2\right) \land \left(\operatorname{IsIndepSet}\left(H, A\right) \land \left(\operatorname{IsIndepSet}\left(H, B\right) \land \left(\forall u \in alpha,\; \operatorname{mem}\left(u, A\right) \Rightarrow \operatorname{degree}\left(H, u\right) = 2\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/BipartiteCompletion.exists_saturating_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha be any finite type with decidable equality, G an actual simple graph on alpha, and A and B actual finite sets. Assume that each part is independent in G, the parts are disjoint and cover every vertex, G is acyclic, every degree is at most two, and card(A) is strictly less than card(B). There exists an actual graph H on exactly alpha containing every edge of G. The graph H is acyclic, every degree is at most two, both original parts remain independent, and every vertex of A has degree exactly two. No decomposition, matching, completion or saturability witness is assumed.

Choose a maximal acyclic, degree-at-most-two, color-preserving extension. If u in A has degree less than two, let C be its actual connected component. The induced graph on C is a tree. Its edge count plus one is its vertex count; its edge count is also the sum of A degrees in C. That sum is strictly less than twice card(A intersect C), so card(B intersect C) is at most card(A intersect C). The full strict B surplus therefore persists outside C. Component closure preserves original degrees under induction. The bipartite degree sums outside C are equal, while the A sum is at most twice its outside cardinality. Consequently some B vertex v outside C has degree less than two. Adding uv preserves both colors and maximum degree, and it cannot form a cycle because its endpoints were unreachable. This contradicts maximality.

All vertices, including all original isolated vertices, remain in the carrier. Original isolates may acquire edges. The empty A case, arbitrary disconnected inputs, and the smallest surplus card(B)=card(A)+1 are included. Already saturated inputs satisfy the conclusion with H=G. The strict inequality is necessary in general: a single edge with one vertex in each part cannot give its A vertex degree two on the same two-vertex carrier.

This is a finite structural extension theorem. It gives no concentration of path components, no signed Catalan comparison with one odd path and isolated vertices, no native triangulation-count identity or numerical extremum, and no resource bound for obtaining a completion. Those require their own mathematical bridges. The proof reuses Mathlib finite maximality, tree edge cardinality, bipartite degree sums, induced degree transport and acyclicity under an edge between unreachable vertices. No literature priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/BipartiteCompletion.exists_saturating_extension`
