# Adjacent supports and harmonic payment

## Abstract

For a connected finite simple graph with maximum degree at most four and at most one original leaf neighbor per vertex, deleting two adjacent nonleaf supports with original pendant neighbors decreases the rational harmonic index by at least 21/20. All degrees in the remaining graph are recomputed, and original pendant edges at retained vertices contribute their actual defect changes.

**Definition 1.1 (Harmonic index).**

Lean statement: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.harmonicIndex`

*Formalization.* `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.harmonicIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite simple graph F, H(F) is the sum of 2/(degree_F(x)+degree_F(y)) over its unordered edges xy. Isolated vertices contribute zero. The arithmetic is rational.

**Definition 1.2 (Actual induced residual).**

Lean statement: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.residual`

*Formalization.* `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph residual(G,X) is the induced graph on the subtype of vertices outside X. It retains every surviving vertex, including isolates, and computes its degrees from the surviving edges.

**Definition 1.3 (Degree defect).**

Lean statement: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.degreeDefect`

*Formalization.* `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.degreeDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write phi(d,e)=(d-e)^2/(2de(d+e)), with subtraction and division in the rational numbers. This expression is symmetric in d,e. On an edge both endpoint degrees are positive.

**Definition 1.4 (Total harmonic defect).**

Lean statement: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.harmonicDefect`

*Formalization.* `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.harmonicDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D(F) is the sum of phi(degree_F(x),degree_F(y)) over the unordered edges of F. Its degrees belong to F, including when F is an induced residual.

**Definition 1.5 (Number of nonisolated vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.nonisolatedCount`

*Formalization.* `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.nonisolatedCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonisolated count of F is the cardinality of the vertices whose degree in F is nonzero.

**Theorem 1.6 (The simultaneous payment estimate).**

$$\forall G \in SimpleGraph(V),\; \forall a \in V,\; \forall b \in V,\; \forall u \in V,\; \forall v \in V,\; ((Connected(G)) \land ((maxDegree(G) \le 4) \land ((\forall x \in V,\; leafCount(G,x) \le 1) \land ((Adj(G,a,b)) \land ((2 \le degree(G,a)) \land ((2 \le degree(G,b)) \land ((degree(G,u) = 1) \land ((Adj(G,a,u)) \land ((degree(G,v) = 1) \land (Adj(G,b,v))))))))))) \Rightarrow (\frac{21}{20} \le H(G)-H(residual(G,\{a,b\})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.adjacent_support_harmonic_payment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every universe and finite vertex type V with decidable equality, let G be a simple graph with decidable adjacency. Assume G is connected, has maximum degree at most four, and every vertex has at most one neighbor of original G-degree one. Let a,b,u,v be vertices with a adjacent to b, degrees of a and b at least two, u of degree one adjacent to a, and v of degree one adjacent to b. Then H(G)-H(G[V\{a,b}]) is at least 21/20. In the formula, leafCount(G,x) counts the neighbors of x with original degree one.

Put X={a,b}. For a retained vertex x write q(x)=|N_G(x)\X|, r(x)=|N_G(x) intersect X|, and t(x)=leafCount(G,x). The equality q+r=degree_G uses one joint loss at x; a shared neighbor has r=2. The two pendant vertices are distinct, survive, and become isolates. If i is the total number of residual isolates, reciprocal-degree accounting gives H(G)-H(G[V\X])=(2+i)/2-(D(G)-D(G[V\X])).

For a retained original nonleaf vertex, the leaf-sensitive capacities c(d,t) for d=2,3,4 and t=0,1 are respectively (0,1/12), (1/30,1/10), and (3/40,13/120). The retained edge charges sum at most r(x)c(d,t); each original retained leaf edge uses its exact phi(d,1)-phi(q,1). Boundary charges cancel these capacities at retained vertices. At each deleted support, reserve its unique pendant edge and its edge to the other support, counting the latter by one half in each directed row. The resulting defect decrease is at most 19/20. Since i is at least two, the harmonic decrease is at least 2-19/20=21/20.

A triangle abc with pendant edges au,bv,cw has H(G)=5/2 and H(G[V\{a,b}])=1. The retained vertex c has joint loss two, and the retained edge cw has defect decrease 1/6, exceeding 1/15. This edge requires the original-leaf charge. Triangles and shared neighbors are allowed; no residual minimum-degree hypothesis is imposed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.adjacent_support_harmonic_payment`
- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.degreeDefect`
- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.harmonicDefect`
- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.harmonicIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.nonisolatedCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacentSupportPayment.residual`
