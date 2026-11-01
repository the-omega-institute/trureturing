# Ordered directed edge-collision counts

## Abstract

Ordered directed edge-collision counts

A walk of length k is a function from Fin(k+1) to the vertex type. Its edge at i is the ordered pair of its vertices at i and i+1. Thus loops are included, the first position is distinguished, and no rotations are identified. Write E(w) for the finite image of the edge map and end(w) for the last vertex. The prefix deletes only the final edge and its terminal vertex. Collision(v,w) means that w starts at v, its prefix edges are pairwise distinct, its final edge occurs in the prefix, and every vertex is visited.

**Definition 1.1 (Ordered vertex walks).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Walk`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Walk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every vertex type V and natural k, Walk(V,k) is the function type Fin(k+1) to V.

**Definition 1.2 (Actual directed edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.edge`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any walk w and i in Fin(k), edge(w,i) is (w(i),w(i+1)), with both vertices interpreted in Fin(k+1).

**Definition 1.3 (Deleting the last edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.initialWalk`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.initialWalk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a walk of length k+1, initialWalk restricts its vertex function to the first k+1 positions.

**Definition 1.4 (First collision at the final edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Collision`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Collision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The walk starts at v, its first k directed edges are distinct, its final edge repeats one of them, and its vertex function is surjective.

**Definition 1.5 (Source edge sequences).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.OrderedEdges`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.OrderedEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An element consists of k+1 ordered pairs. The first tail is v, and each edge head equals the next edge tail.

**Definition 1.6 (Reconstructing vertex walks).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.orderedEdgesEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.orderedEdgesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every V, v in V and natural k, based vertex walks of length k+1 are equivalent to OrderedEdges(V,v,k). The inverse writes v followed by the successive edge heads. Both composites are the identity.

**Definition 1.7 (Collision directly on ordered edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.SourceCollision`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.SourceCollision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first k edges are distinct, the last repeats one of them, and each vertex is either v or a head of one of the k+1 edges.

**Definition 1.8 (Exact source collision correspondence).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.sourceCollisionEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.sourceCollisionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every V, v and k, collision vertex walks of length k+1 are equivalent to ordered edge sequences satisfying SourceCollision. The equivalence preserves the distinguished start, adjacency, distinctness, final repetition and vertex coverage. For finite V both carriers are finite and consequently have equal cardinalities.

**Theorem 1.9 (The two omitted-edge configurations).**

$$\forall n \in \mathrm{Nat},\; 2 \le n \Rightarrow \left(\forall w \in \mathrm{Walk}\left(\mathrm{Fin}\left(n\right), n \cdot n - 1\right),\; \mathrm{Injective}\left(\mathrm{edge}\left(w\right)\right) \Rightarrow \left(\mathrm{Surjective}\left(w\right) \land \left(\exists a \in \mathrm{Fin}\left(n\right),\; \exists b \in \mathrm{Fin}\left(n\right),\; \mathrm{E}\left(w\right) = \mathrm{erase}\left(\mathrm{univ}, \mathrm{pair}\left(a, b\right)\right) \land \left(\left(b = \mathrm{at}\left(w, 0\right) \land \mathrm{end}\left(w\right) = a\right) \lor \left(a = b \land \left(\left(\neg a = \mathrm{at}\left(w, 0\right)\right) \land \mathrm{end}\left(w\right) = \mathrm{at}\left(w, 0\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.prefix_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A trail of length n*n-1 on Fin(n), for n at least two, omits a unique ordered edge (a,b). Summing outgoing minus incoming incidences along the walk telescopes to the difference between its start and endpoint indicators. Summing over every directed pair gives zero, so removing (a,b) leaves the reverse indicator difference. Evaluating this identity at a and b leaves exactly two possibilities: b is the start and a the endpoint, or the omitted edge is a loop at another vertex and the walk is closed. Every vertex occurs because at least one of its n outgoing edges survives the single deletion.

**Theorem 1.10 (The actual prefix of an edge-collision walk).**

$$\forall n \in \mathrm{Nat},\; 2 \le n \Rightarrow \left(\forall v \in \mathrm{Fin}\left(n\right),\; \forall w \in \mathrm{Walk}\left(\mathrm{Fin}\left(n\right), n \cdot n - 1 + 1\right),\; \mathrm{Collision}\left(v, w\right) \Rightarrow \left(\mathrm{Surjective}\left(\mathrm{prefix}\left(w\right)\right) \land \left(\exists a \in \mathrm{Fin}\left(n\right),\; \exists b \in \mathrm{Fin}\left(n\right),\; \mathrm{E}\left(\mathrm{prefix}\left(w\right)\right) = \mathrm{erase}\left(\mathrm{univ}, \mathrm{pair}\left(a, b\right)\right) \land \left(\left(b = v \land \mathrm{end}\left(\mathrm{prefix}\left(w\right)\right) = a\right) \lor \left(a = b \land \left(\left(\neg a = v\right) \land \mathrm{end}\left(\mathrm{prefix}\left(w\right)\right) = v\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collision_prefix_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an edge-collision walk of length (n*n-1)+1, the same alternatives hold for its actual prefix with the specified starting vertex v. This length equals n*n for n at least two. The prefix already visits every vertex. The cardinality argument below retains these two classes separately.

**Definition 1.11 (Full ordered Euler walks).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Euler`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Euler` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Euler(n,v) consists of actual walks of length n*n starting at v whose edge map is bijective onto Fin(n) times Fin(n). The incidence sum proves that every such walk ends at v, and surjectivity of the edge map proves that it visits every vertex.

**Definition 1.12 (Appending the repeated final edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.longCollisionEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.longCollisionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n and v in Fin(n), collision walks of length n*n+1 are equivalent to Euler(n,v) times Fin(n). Delete the final edge in one direction. In the other, append the selected destination to the full Euler walk. All directed edges have already occurred, so the appended edge repeats one. The two operations are inverse on linear ordered walks.

**Definition 1.13 (The literal collision count).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collisionCount`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collisionCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value at total length zero is zero. At length k+1 the value is the finite cardinality of the source's ordered edge sequences satisfying SourceCollision, with fixed start v on n labeled vertices.

**Definition 1.14 (The Euler-walk count).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.eulerCount`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.eulerCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite cardinality of Euler(n,v), with the first vertex and cut fixed.

**Theorem 1.15 (The denominator count).**

$$\forall n \in \mathrm{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \mathrm{collisionCount}\left(n, v, n \cdot n + 1\right) = n \cdot \mathrm{eulerCount}\left(n, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.long_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the exact source collision correspondence and the append/delete equivalence, then take finite cardinalities. The equality supplies the denominator factor n without assuming a factorial formula. The numerator and positivity are supplied separately below.

**Definition 1.16 (Inserting at a linear cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.insertLoop`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.insertLoop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every vertex type V, natural k, walk w of length k and cut p in Fin(k+1), insertLoop duplicates w(p) immediately after p. It inserts the loop (w(p),w(p)); every other edge retains its position through the order-preserving map skipping p.

**Definition 1.17 (Deleting a marked loop).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.removeLoop`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.removeLoop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every V, k, walk w of length k+1 and edge position p, removeLoop deletes the head of that edge. If the marked edge is a loop, deletion and insertion are inverse.

**Definition 1.18 (Trails missing one specified loop).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.MissingLoop`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.MissingLoop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n, fixed start v and vertex a, MissingLoop(n,v,a) consists of length n*n-1 walks starting at v with injective edge map and edge image exactly all directed pairs except (a,a).

**Definition 1.19 (Retaining the insertion cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.MarkedLoop`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.MarkedLoop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n, v and a, MarkedLoop(n,v,a) pairs a MissingLoop trail with a vertex position p at which the trail equals a. Positions remain distinct even when their vertex values agree.

**Definition 1.20 (The marked loop bijection).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.loopInsertionEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.loopInsertionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n at least two and all v,a in Fin(n), inserting the missing loop at the marked cut is an equivalence from MarkedLoop(n,v,a) to Euler(n,v). The inverse locates the unique loop (a,a), deletes its head vertex, and retains its position. The construction applies also to a=v, retaining both boundary cuts when distinct.

**Theorem 1.21 (Counting the noninitial loop cuts).**

$$\forall n \in \mathrm{Nat},\; 2 \le n \Rightarrow \left(\forall v \in \mathrm{Fin}\left(n\right),\; \forall a \in \mathrm{Fin}\left(n\right),\; \left(\neg a = v\right) \Rightarrow \mathrm{eulerCount}\left(n, v\right) = \left(n - 1\right) \cdot \mathrm{card}\left(\mathrm{MissingLoop}\left(n, v, a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.loop_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a different from v, a missing-loop trail is closed at v, so neither boundary cut is at a. Its cuts at a correspond bijectively to its outgoing edges (a,b), b different from a. There are exactly n-1. The marked-loop bijection therefore gives E=(n-1)L(a).

**Definition 1.22 (Prefixes completed by their closing edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.ReturnTrail`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.ReturnTrail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n and v, ReturnTrail(n,v) consists of length n*n-1 trails starting at v whose unique omitted edge goes from their endpoint back to v.

**Definition 1.23 (Completing the return prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.returnTrailEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.returnTrailEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n at least two and v in Fin(n), append v to a ReturnTrail to obtain an Euler walk. Deleting the last edge is the inverse. This counts these linear prefixes by E.

**Theorem 1.24 (The numerator count).**

$$\forall n \in \mathrm{Nat},\; 2 \le n \Rightarrow \left(\forall v \in \mathrm{Fin}\left(n\right),\; \mathrm{collisionCount}\left(n, v, n \cdot n\right) = \left(2 \cdot n - 1\right) \cdot \mathrm{eulerCount}\left(n, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.short_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition almost-complete collision prefixes by the omitted-edge classification. A ReturnTrail has n-1 repeated-edge choices, excluding the omitted edge back to v. A trail missing (a,a), a different from v, ends at v and has all n final choices. The loop bijections give (n-1)L(a)=E; summing over the n-1 vertices and cancelling n-1 gives the sum of L(a) equal to E. Thus the numerator is (n-1)E+nE=(2n-1)E.

**Theorem 1.25 (Constructing a full Euler walk).**

$$\forall n \in \mathrm{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \mathrm{Nonempty}\left(\mathrm{Euler}\left(n, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.euler_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with the zero-length walk at v. Extend the trail by an unused outgoing edge, reserving each edge (a,v) until every other outgoing edge from a is used. If the endpoint has no unused departure, incidence balance forces it to be v. All edges entering v must then have occurred; the reserved-last-exit invariant forces every directed edge to have occurred. Hence the construction extends until exactly n*n distinct edges are used. This works for every n with a specified v in Fin(n).

**Theorem 1.26 (Positive source denominator).**

$$\forall n \in \mathrm{Nat},\; 2 \le n \Rightarrow \left(\forall v \in \mathrm{Fin}\left(n\right),\; 0 < \mathrm{collisionCount}\left(n, v, n \cdot n + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.long_count_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed Euler walk makes its finite count positive. The exact denominator bijection gives T(n,n*n+1)=nE, which is positive for n at least two.

**Theorem 1.27 (The exact all-n rational ratio).**

$$\forall n \in \mathrm{Nat},\; 2 \le n \Rightarrow \left(\forall v \in \mathrm{Fin}\left(n\right),\; \frac{\mathrm{collisionCount}\left(n, v, n \cdot n\right)}{\mathrm{collisionCount}\left(n, v, n \cdot n + 1\right)} = \frac{2 \cdot n - 1}{n}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collision_ratio` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396659-edge-collision-ratio` (proved) by `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collision_ratio` and `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.long_count_positive`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396659-edge-collision-ratio","declaration_gid":"D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collision_ratio","resolution_kind":"proved"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396659-edge-collision-ratio","declaration_gid":"D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.long_count_positive","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every n at least two and arbitrary fixed v in Fin(n), substitute the two source count identities and cancel the positive Euler count. Both carriers count ordered walks with loops and vertex coverage; no rotation quotient or separate factorial count is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Collision`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Euler`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.MarkedLoop`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.MissingLoop`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.OrderedEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.ReturnTrail`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.SourceCollision`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.Walk`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collisionCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collision_prefix_structure`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.collision_ratio`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.eulerCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.euler_nonempty`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.initialWalk`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.insertLoop`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.longCollisionEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.long_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.long_count_positive`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.loopInsertionEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.loop_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.orderedEdgesEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.prefix_structure`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.removeLoop`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.returnTrailEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.short_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.sourceCollisionEquiv`
