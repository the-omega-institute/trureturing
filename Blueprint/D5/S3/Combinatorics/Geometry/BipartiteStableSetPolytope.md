# Independent-set polytopes on the original vertex labels

## Abstract

Bipartite graphs are exactly the finite graphs whose independent-set hull is described by bounds and edge inequalities.

Let V be any universe-polymorphic vertex type and G a native simple graph on V. All vectors are functions V to the reals. The finite-type hypothesis appears only in the characterization; no inhabitance, connectedness, edge, enumeration or rational-coordinate assumption is imposed.

**Definition 1.1 (Finite-set indicators).**

$$\forall V \in Type,\; \forall A \in Finset(V),\; vertexIndicator(A) = indicator((A:Set(V)), constant(1))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.vertexIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

vertexIndicator(A) is the native Set.indicator of the underlying set of A, with value one on A and zero elsewhere. It retains every original label, including isolated vertices.

**Definition 1.2 (The actual independent-set hull).**

$$\forall V \in Type,\; \forall G \in SimpleGraph(V),\; stableSetPolytope(G) = convexHull(Real, \{vertexIndicator(A) | A:Finset(V), IsIndepSet(G, (A:Set(V)))\})$$

*Formalization.* `D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.stableSetPolytope` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Chvatal (1975). *On certain polytopes associated with graphs*. URL: <https://doi.org/10.1016/0095-8956(75)90041-6>.

*Commentary.*

Take the real convex hull of the range of vertexIndicator on the subtype of independent Finsets. Independence is the native graph predicate on the underlying set. This is a set of actual real vectors on V.

**Definition 1.3 (Bounds and edge inequalities).**

$$\forall V \in Type,\; \forall G \in SimpleGraph(V),\; \forall x \in V\to Real,\; x \in edgeRegion(G) \Leftrightarrow \left(\left(\forall v \in V,\; 0 \le x(v) \land x(v) \le 1\right) \land \left(\forall v \in V,\; \forall w \in V,\; Adj(G, v, w) \Rightarrow x(v)+x(w) \le 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.edgeRegion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every coordinate lies between zero and one. Every adjacent pair has coordinate sum at most one. Upper bounds at isolated vertices are part of the definition.

**Theorem 1.4 (The bipartite characterization).**

$$\forall V \in Type,\; [Finite(V)] \forall G \in SimpleGraph(V),\; stableSetPolytope(G) = edgeRegion(G) \Leftrightarrow IsBipartite(G)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.stableSetPolytope_eq_edgeRegion_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Chvatal (1975). *On certain polytopes associated with graphs*. URL: <https://doi.org/10.1016/0095-8956(75)90041-6>.

*Commentary.*

For every finite V and every simple graph G on V, equality of these two sets of real vectors is equivalent to native bipartiteness. The statement includes empty vertex types, isolated vertices and disconnected graphs.

Every independent indicator satisfies the inequalities, and the inequality region is convex. For the converse inclusion under bipartiteness, fix a total two-coloring and complement the coordinates in one color. The transformed vector lies in the unit cube and increases along edges oriented from the first color to the second. Its positive support defines an independent indicator after the complement is undone. Peel off the minimum positive level delta. If delta equals one, the vector is already that indicator. Otherwise subtract delta on the positive support and divide by one minus delta; the new positive support is strictly smaller. Induction reconstructs a convex combination on the same V. On the complemented color the reconstruction uses delta times (one minus the support indicator), plus one minus delta times (one minus the residual coordinate). Thus isolated labels and tied minimum levels are retained.

For necessity, the constant one-half vector belongs to the inequality region. A finite convex representation in independent indicators has a positive coefficient. Fix one such coefficient before considering any edge. Equality in the weighted edge bound forces that same indicator to meet every edge in exactly one endpoint. Its underlying set and complement form a bipartition. Selection uses the convex-combination index type, so it also applies when V is empty. The construction establishes the classical graph-polyhedral characterization; no claim of mathematical originality is made. The existing Chvatal note records the general perfect-graph clique description and its primary-text access boundary. This is a related classical source; the Lean proof here is the finite support construction just described.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.edgeRegion`
- Truth anchor: `D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.stableSetPolytope`
- Truth anchor: `D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.stableSetPolytope_eq_edgeRegion_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope.vertexIndicator`
