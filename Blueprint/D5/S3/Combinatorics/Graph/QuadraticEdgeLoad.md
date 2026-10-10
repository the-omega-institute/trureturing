# Quadratic edge loads and regular components

## Abstract

The smallest possible maximum of the squared edge-share loads reaches one quarter of the maximum degree exactly when a connected component has that constant degree.

Let G be a finite simple undirected graph with a nonempty vertex type V. The coordinate a(b,c) denotes the share paid by b on the edge joining b and c. Coordinates on nonedges are bounded extensions and never enter the loads. Every allocation on oriented edges extends by assigning one half on nonedges; restriction recovers the original allocation with identical loads.

**Definition 1.1 (Actual feasible shares).**

$$\forall V \in \mathrm{Type},\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall a \in V \to \left(V \to \mathrm{Real}\right),\; \mathrm{Feasible}\left(G, a\right) \Leftrightarrow \left(\left(\forall b \in V,\; \forall c \in V,\; 0 \le a\left(b, c\right) \land a\left(b, c\right) \le 1\right) \land \left(\forall b \in V,\; \forall c \in V,\; \mathrm{Adj}\left(G, b, c\right) \Rightarrow a\left(b, c\right) + a\left(c, b\right) = 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.Feasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All coordinates lie in the closed unit interval. Opposite shares add to one on every edge; no opposite-share equation is imposed on nonedges.

**Definition 1.2 (Vertex load).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] \forall a \in V \to \left(V \to \mathrm{Real}\right),\; \forall b \in V,\; \mathrm{load}\left(G, a, b\right) = \sum_{c \in \mathrm{neighborFinset}\left(G, b\right)} a\left(b, c\right)^{2}$$

*Formalization.* `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.load` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex pays the sum of the squares of its incident shares. An isolated vertex has load zero.

**Definition 1.3 (Maximum load).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] [\mathrm{Nonempty}\left(V\right)] \forall a \in V \to \left(V \to \mathrm{Real}\right),\; \mathrm{maxLoad}\left(G, a\right) = \max_{b : V} \mathrm{load}\left(G, a, b\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.maxLoad` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum ranges over all vertices, including isolated vertices.

**Definition 1.4 (The optimization value).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] [\mathrm{Nonempty}\left(V\right)] \mathrm{kappa}\left(G\right) = \mathrm{sInf}\left(\{r : \mathrm{Real} | \exists a \in V \to \left(V \to \mathrm{Real}\right),\; \mathrm{Feasible}\left(G, a\right) \land \mathrm{maxLoad}\left(G, a\right) = r\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Kappa is the infimum of actual maximum loads over feasible allocations. The following minimum-attainment statement identifies it with a minimum.

**Theorem 1.5 (An actual minimum).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] [\mathrm{Nonempty}\left(V\right)] \exists a \in V \to \left(V \to \mathrm{Real}\right),\; \mathrm{Feasible}\left(G, a\right) \land \mathrm{maxLoad}\left(G, a\right) = \mathrm{kappa}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.minimum_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The feasible set is a closed subset of the finite product of closed unit intervals and contains the equal-share allocation. Each load is continuous, as is their finite maximum. Compact minimum attainment therefore applies.

**Theorem 1.6 (A strict allocation without a regular component).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] [\mathrm{Nonempty}\left(V\right)] \neg (\exists C \in \mathrm{ConnectedComponent}\left(G\right),\; \forall b \in V,\; b \in \mathrm{supp}\left(C\right) \Rightarrow \mathrm{degree}\left(G, b\right) = \mathrm{maxDegree}\left(G\right)) \Rightarrow \left(\exists a \in V \to \left(V \to \mathrm{Real}\right),\; \mathrm{Feasible}\left(G, a\right) \land \left(\forall b \in V,\; \mathrm{load}\left(G, a, b\right) < \frac{\mathrm{maxDegree}\left(G\right)}{4}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.strict_allocation_of_no_regular_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If no component is maximum-degree regular, every vertex can reach a vertex whose degree is smaller than the maximum D. Let l(b) be the shortest walk length to such a vertex. Adjacent levels differ by at most one, and every positive level has a neighbor one level lower. For j at least one, put epsilon(j) equal to one half times (1/(8D)) to the power j. On an edge from level j to level j minus one, the higher vertex pays one half minus epsilon(j), and the lower vertex pays one half plus epsilon(j). Equal levels pay one half. A positive-level vertex saves at least epsilon(j)/2 on a descending edge, while all increases together are at most epsilon(j)/4. A level-zero vertex has a missing degree unit; its total increase is at most one eighth. Every vertex load is consequently strictly below D/4.

**Theorem 1.7 (The complete equality characterization).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] [\mathrm{Nonempty}\left(V\right)] \mathrm{kappa}\left(G\right) = \frac{\mathrm{maxDegree}\left(G\right)}{4} \Leftrightarrow \left(\exists C \in \mathrm{ConnectedComponent}\left(G\right),\; \forall b \in V,\; b \in \mathrm{supp}\left(C\right) \Rightarrow \mathrm{degree}\left(G, b\right) = \mathrm{maxDegree}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.maximum_degree_equality_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal shares give the universal upper bound D/4. In a D-regular component, the two squared shares on each edge sum to at least one half, so the average vertex load is at least D/4 for every feasible allocation. Conversely, the strict allocation above has a strict maximum because the vertex set is finite. The equivalence includes disconnected graphs and arbitrary isolated vertices. When D is zero, every component is an isolated zero-regular vertex and kappa is zero. No dual optimization identity is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.Feasible`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.kappa`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.load`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.maxLoad`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.maximum_degree_equality_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.minimum_attained`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.strict_allocation_of_no_regular_component`
