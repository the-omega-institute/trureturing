# Trivalent coordination in the elongated triangular dual

## Abstract

The face adjacency graph of the elongated triangular tiling, centered at an upward triangle, has the coordination generating function conjectured by Colin Barker.

**Definition 1.1 (The three face types).**

$$Vertex = \{\operatorname{Vertex.S}\left(m, k\right), \operatorname{Vertex.U}\left(m, k\right), \operatorname{Vertex.D}\left(m, k\right) \mid m,k \in \mathbb{Z}\}$$

*Formalization.* `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

Vertex is the free inductive type with constructors Vertex.S, Vertex.U and Vertex.D. Each constructor takes two integers m and k. The constructors are injective, their ranges are disjoint, and every vertex has exactly one such form. S denotes a square, U an upward triangle and D a downward triangle.

**Definition 1.2 (The square constructor).**

$$\operatorname{Vertex.S}: \mathbb{Z} \Rightarrow \mathbb{Z} \Rightarrow Vertex$$

*Formalization.* `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

S(m,k) is the square in strip m at position k.

**Definition 1.3 (The upward triangle constructor).**

$$\operatorname{Vertex.U}: \mathbb{Z} \Rightarrow \mathbb{Z} \Rightarrow Vertex$$

*Formalization.* `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

U(m,k) is the upward triangle in triangular strip m at position k.

**Definition 1.4 (The downward triangle constructor).**

$$\operatorname{Vertex.D}: \mathbb{Z} \Rightarrow \mathbb{Z} \Rightarrow Vertex$$

*Formalization.* `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

D(m,k) is the downward triangle in triangular strip m at position k.

**Definition 1.5 (The face adjacency graph).**

$$\forall v: Vertex, (\forall w: Vertex, ((\operatorname{SimpleGraph.Adj}\left(graph, v, w\right)) \iff ((\exists m: \mathbb{Z}, (\exists k: \mathbb{Z}, (((v = \operatorname{Vertex.S}\left(m, k\right)) \land (w = \operatorname{Vertex.S}\left(m, k + 1\right))) \lor (((v = \operatorname{Vertex.S}\left(m, k\right)) \land (w = \operatorname{Vertex.U}\left(m, k\right))) \lor (((v = \operatorname{Vertex.S}\left(m + 1, k\right)) \land (w = \operatorname{Vertex.D}\left(m, k\right))) \lor (((v = \operatorname{Vertex.U}\left(m, k\right)) \land (w = \operatorname{Vertex.D}\left(m, k\right))) \lor ((v = \operatorname{Vertex.U}\left(m, k\right)) \land (w = \operatorname{Vertex.D}\left(m, k - 1\right))))))))) \lor (\exists m: \mathbb{Z}, (\exists k: \mathbb{Z}, (((w = \operatorname{Vertex.S}\left(m, k\right)) \land (v = \operatorname{Vertex.S}\left(m, k + 1\right))) \lor (((w = \operatorname{Vertex.S}\left(m, k\right)) \land (v = \operatorname{Vertex.U}\left(m, k\right))) \lor (((w = \operatorname{Vertex.S}\left(m + 1, k\right)) \land (v = \operatorname{Vertex.D}\left(m, k\right))) \lor (((w = \operatorname{Vertex.U}\left(m, k\right)) \land (v = \operatorname{Vertex.D}\left(m, k\right))) \lor ((w = \operatorname{Vertex.U}\left(m, k\right)) \land (v = \operatorname{Vertex.D}\left(m, k - 1\right))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.graph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

The displayed five edge families and their reversals are all the edges. Thus a square S(m,k) has square neighbours S(m,k−1) and S(m,k+1), and triangular neighbours U(m,k) and D(m−1,k). An upward triangle has neighbours S(m,k), D(m,k−1), D(m,k). A downward triangle has neighbours S(m+1,k), U(m,k), U(m,k+1).

**Definition 1.6 (The upward triangular root).**

$$root = \operatorname{Vertex.U}\left(0, 0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.root` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

This node has degree three.

**Definition 1.7 (The genuine graph distance).**

$$\forall v: Vertex, (\operatorname{distance}\left(v\right) = \operatorname{SimpleGraph.dist}\left(graph, root, v\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.distance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

SimpleGraph.dist is the minimum walk length. The distance proof constructs a walk from the root to every vertex.

**Definition 1.8 (The finite distance-shell cardinality).**

$$\forall n: \mathbb{N}, (\operatorname{a}\left(n\right) = \operatorname{Set.ncard}\left(\{v: Vertex \mid \operatorname{distance}\left(v\right) = n\}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

The radius n ranges over all natural numbers, including zero. The proof identifies each shell with a finite set of coordinates; Set.ncard therefore counts a proved-finite shell.

**Theorem 1.9 (Barker's formal series identity).**

$$(1 - \operatorname{PowerSeries.X})^{2} \cdot (1 + \operatorname{PowerSeries.X} + \operatorname{PowerSeries.X}^{2}) \cdot \operatorname{PowerSeries.mk}\left(\lambda n \mapsto (\operatorname{a}\left(n\right): \mathbb{Z})\right) = 1 + 2 \cdot \operatorname{PowerSeries.X} + 4 \cdot \operatorname{PowerSeries.X}^{2} + 4 \cdot \operatorname{PowerSeries.X}^{3} + 3 \cdot \operatorname{PowerSeries.X}^{4} + 2 \cdot \operatorname{PowerSeries.X}^{5} - 2 \cdot \operatorname{PowerSeries.X}^{8}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.result` (`✓ std3`). ∎

*Resolves.* `Problems/sloane298022` (proved) by `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sloane298022","declaration_gid":"D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298022: coordination sequence of Dual(3^3.4^2) at a trivalent node*. URL: <https://oeis.org/A298022>.

*Commentary.*

For an integer interval [l,u], write its distance from k as max(0,l−k,k−u). At S(m,k) the potential is 1−3m plus the distance from k to [0,−m] when m≤0, and 3m−1 plus the distance to [−m,0] when m>0. At U(m,k), for m<0 use −3m and [0,−m]; for m>0 use 3m and [−m,0]. At U(0,k) use min(2|k|,|k|+2). At D(m,k), for m<0 use −3m−1 and [0,−m−1]; for m>0 use 3m+1 and [−m−1,0]. At D(0,k) use min(|2k+1|,min(|k|,|k+1|)+3).

The potential is nonnegative and is zero precisely at U(0,0). For every edge, either endpoint's potential is at most one plus the other's. At every positive-potential vertex one of the displayed neighbours decreases the potential by exactly one. Strong induction constructs an attaining walk. The potential bound on walk length gives the reverse inequality, so the potential equals the graph distance.

Separate the vertices into six infinite strip families and the central U and D rows. For r≥0 the strip representatives are S(−r,j), S(r+1,j−r−1), U(−r−1,j), U(r+1,j−r−1), D(−r−1,j), D(r+1,j−r−2). Their pairs (c,L) are respectively (1,1), (2,2), (3,2), (3,2), (2,1), (4,3). Each has distance 3r+c+max(0,−j,j−r−L+1). At radius 3r+c its j interval is [0,r+L−1], containing r+L points; at a larger radius it has exactly two points, one on each side. No point occurs at a smaller radius.

Consequently a strip contributes 2⌊(n+2−c)/3⌋, with truncated natural subtraction before division, and an additional (n−c)/3+L when c≤n and n−c is divisible by three. This follows by summing the row cardinalities over 0≤r≤n. The central U row contributes one at n=0, two at n=2, and two at every n≥4. The central D row contributes two at n=1, two at n=3, and two at every n≥5.

For n≥5 the total is 14⌊n/3⌋ plus zero, five or nine according as n modulo three is zero, one or two. The first nine coefficients and this all-radius formula give the coefficient identity for (1−X)(1−X³), equal to (1−X)²(1+X+X²). Equality of coefficients proves the displayed identity in integer formal power series.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.D`
- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.S`
- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.U`
- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.Vertex`
- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.a`
- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.distance`
- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.graph`
- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.result`
- Truth anchor: `D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination.root`
- Dependency: [D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation](../Combinatorics/PositionSets/VertexPositionRatioRefutation.md)
