# Optimal induced maximum degree at 260 vertices

## Abstract

The minimum induced maximum degree on 260 vertices of the nine-cube is four.

Write Q₉[U] for the graph induced by a vertex set U in the nine-cube and Δ for maximum degree. In the notation of Hong–Wu–Xia, fₖ(Q₉) minimizes Δ over induced subgraphs on 256 + k vertices. The two statements give f₄(Q₉) = 4.

**Theorem 1.1 (Every 260-vertex induced subgraph has maximum degree at least four).**

$$\forall U \subseteq V(Q_9), |U|=260 \longrightarrow 4 \le \Delta(Q_9[U])$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeThresholdFour.four_le_maxDegree_of_card_260` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose Q₉[U] is subcubic and |U| = 260. The small-order classification gives size 54 or at least 72 for every Huang-balanced cubic component. The Gray54 extension obstruction bounds |U| by 257 if such a component has 54 vertices. Thus each Huang-balanced cubic component has at least 72 vertices.

The positive Huang eigenspace has dimension 256. Restricting to the 252 vertices outside U leaves a kernel of dimension at least four by rank-nullity. A supported eigenvector that is nonzero on a component saturates degree three there and gives Huang balance. Evaluation at one vertex of each balanced cubic component is injective on the supported eigenspace, so there are at least four such components. Their disjoint vertex sets would require at least 288 vertices.

**Theorem 1.2 (A 260-vertex induced subgraph attains maximum degree four).**

$$\exists U \subseteq V(Q_9), |U|=260 \land \Delta(Q_9[U])=4$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeThresholdFour.exists_card_260_maxDegree_eq_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take both ninth-coordinate lifts of the 130-vertex set of Hong–Wu–Xia, Proposition 6.2. The explicit lifted set has 260 vertices and maximum degree at most four. The lower bound gives equality (https://arxiv.org/html/2610.09483v1#S6.Thmtheorem2).

The original Hong–Wu–Xia question about f₂(Q₉) at 258 vertices remains open (arXiv:2610.09483v1, §7, Problem 2, https://arxiv.org/html/2610.09483v1#Thmproblem2).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeThresholdFour.exists_card_260_maxDegree_eq_four`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeThresholdFour.four_le_maxDegree_of_card_260`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound](Q9Gray54ExtensionBound.md)
