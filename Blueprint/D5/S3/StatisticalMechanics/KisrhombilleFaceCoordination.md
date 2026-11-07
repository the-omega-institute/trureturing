# Face-rooted kisrhombille coordination

## Abstract

The coordination sequence of the simplex-inclusion graph of the triangular lattice, centered at an upward face, satisfies Barker's formal generating-function identity.

Coordinates i and j are integers. Products associate to the right: a simplex is (t,(i,j)). The six values of t in Fin 6, numbered zero through five, denote a vertex V, horizontal edge H, vertical edge B, diagonal edge D, upward face U and downward face W, respectively. Integer pairs are lattice vertices. The triangular lattice has difference vectors ±(1,0), ±(0,1), ±(1,−1). Subset means inclusion of the finite vertex sets, including equality. The graph also requires distinct simplex labels.

**Definition 1.1 (The nonempty simplices).**

$$Simplex = \operatorname{Fin}\left(6\right) \times (\mathbb{Z} \times (\mathbb{Z}))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.Simplex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

Every edge and face occurs once in these coordinates. An edge has two vertices and a face has three. The support equations specify the literal simplices.

**Definition 1.2 (The six finite supports).**

$$\forall i: \mathbb{Z}, (\forall j: \mathbb{Z}, ((\operatorname{support}\left((0, (i, j))\right) = \{(i, j)\}) \land ((\operatorname{support}\left((1, (i, j))\right) = \{(i, j), (i + 1, j)\}) \land ((\operatorname{support}\left((2, (i, j))\right) = \{(i, j), (i, j + 1)\}) \land ((\operatorname{support}\left((3, (i, j))\right) = \{(i + 1, j), (i, j + 1)\}) \land ((\operatorname{support}\left((4, (i, j))\right) = \{(i, j), (i + 1, j), (i, j + 1)\}) \land (\operatorname{support}\left((5, (i, j))\right) = \{(i + 1, j), (i, j + 1), (i + 1, j + 1)\})))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.support` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

Each displayed brace is a Finset of integer pairs. U(i,j) has vertices (i,j), (i+1,j), (i,j+1); W(i,j) has vertices (i+1,j), (i,j+1), (i+1,j+1). All six kinds of support are nonempty.

**Definition 1.3 (The simplex-inclusion graph).**

$$\forall s: Simplex, (\forall t: Simplex, ((\operatorname{SimpleGraph.Adj}\left(graph, s, t\right)) \iff ((s \neq t) \land ((\operatorname{support}\left(s\right) \subseteq \operatorname{support}\left(t\right)) \lor (\operatorname{support}\left(t\right) \subseteq \operatorname{support}\left(s\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.graph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

Any two distinct comparable simplices are adjacent. In particular, a vertex and a containing face are adjacent even without specifying an intermediate edge. This is the vertex-edge graph of the barycentric subdivision. An upward face is adjacent to its three vertices and its three edges.

**Definition 1.4 (The specified upward face).**

$$root = (4, (0, 0))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.root` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

The root is U(0,0), a hexavalent node.

**Definition 1.5 (Minimum walk length).**

$$\forall s: Simplex, (\operatorname{distance}\left(s\right) = \operatorname{SimpleGraph.dist}\left(graph, root, s\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.distance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

Distance is SimpleGraph.dist, the genuine shortest-walk distance. Paths from the root to every simplex are constructed in the proof, so no disconnected-distance convention contributes to a shell.

**Definition 1.6 (The literal coordination sequence).**

$$\forall n: \mathbb{N}, (\operatorname{a}\left(n\right) = \operatorname{Set.ncard}\left(\{s: Simplex \mid \operatorname{distance}\left(s\right) = n\}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

Set.ncard is the natural cardinality of the displayed set. Every shell is proved finite by containment in a finite coordinate box. Radius zero is included and contains exactly the root.

**Definition 1.7 (Translated cut rectangles).**

$$\forall A: \mathbb{N}, (\forall B: \mathbb{N}, (\forall l: \mathbb{N}, (\forall r: \mathbb{N}, (\forall i0: \mathbb{Z}, (\forall j0: \mathbb{Z}, (\operatorname{polygon}\left(A, B, l, r, i0, j0\right) = \operatorname{Finset.image}\left((\lambda p \mapsto (i0 + (p.1: \mathbb{Z}), j0 + (p.2: \mathbb{Z}))), \operatorname{cutRectangle}\left(A, B, l, r\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.polygon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

The natural rectangle 0≤u≤A, 0≤v≤B is cut by deleting u+v<l and (A−u)+(B−v)<r. This finite set is cutRectangle(A,B,l,r). The image map casts each natural coordinate to an integer and translates by (i0,j0). The projections p.1 and p.2 are the first and second components.

**Theorem 1.8 (Six inequalities for polygon membership).**

$$\forall A: \mathbb{N}, (\forall B: \mathbb{N}, (\forall l: \mathbb{N}, (\forall r: \mathbb{N}, (\forall i0: \mathbb{Z}, (\forall j0: \mathbb{Z}, ((l \leq A + 1) \longrightarrow ((l \leq B + 1) \longrightarrow ((r \leq A + 1) \longrightarrow ((r \leq B + 1) \longrightarrow (\forall p: \mathbb{Z} \times (\mathbb{Z}), ((p \in \operatorname{polygon}\left(A, B, l, r, i0, j0\right)) \iff ((i0 \leq p.1) \land ((p.1 \leq i0 + (A: \mathbb{Z})) \land ((j0 \leq p.2) \land ((p.2 \leq j0 + (B: \mathbb{Z})) \land (((l: \mathbb{Z}) \leq p.1 + p.2 - i0 - j0) \land (p.1 + p.2 - i0 - j0 + (r: \mathbb{Z}) \leq (A: \mathbb{Z}) + (B: \mathbb{Z}))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.polygon_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

Each corner fits in the rectangle when its size is at most A+1 and B+1. Under these four natural inequalities, membership is equivalent to the displayed six integer inequalities. The last two bounds remove the two triangular corners.

**Theorem 1.9 (Polygon cardinality).**

$$\forall A: \mathbb{N}, (\forall B: \mathbb{N}, (\forall l: \mathbb{N}, (\forall r: \mathbb{N}, (\forall i0: \mathbb{Z}, (\forall j0: \mathbb{Z}, ((l \leq A + 1) \longrightarrow ((l \leq B + 1) \longrightarrow ((r \leq A + 1) \longrightarrow ((r \leq B + 1) \longrightarrow ((l + r \leq A + B + 1) \longrightarrow (2 \cdot (\operatorname{Finset.card}\left(\operatorname{polygon}\left(A, B, l, r, i0, j0\right)\right): \mathbb{Z}) = 2 \cdot \left((A: \mathbb{Z}) + 1\right) \cdot \left((B: \mathbb{Z}) + 1\right) - (l: \mathbb{Z}) \cdot \left((l: \mathbb{Z}) + 1\right) - (r: \mathbb{Z}) \cdot \left((r: \mathbb{Z}) + 1\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.polygon_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

When l+r≤A+B+1, the removed corners are disjoint. Their doubled sizes are l(l+1) and r(r+1). Subtracting them from twice the rectangle size gives the formula. The cardinality is cast to an integer before multiplication.

**Theorem 1.10 (Finiteness of every distance shell).**

$$\forall n: \mathbb{N}, (\operatorname{Set.Finite}\left(\{s: Simplex \mid \operatorname{distance}\left(s\right) = n\}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.shell_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

Every shell is contained in the finite coordinate ball of the same radius. Here distance uses the upward-face root, and n is any natural number.

**Theorem 1.11 (Barker's generating-function identity).**

$$(1 - (\operatorname{PowerSeries.X}: \operatorname{PowerSeries}\left(\mathbb{Z}\right))^{2})^{2} \cdot \operatorname{PowerSeries.mk}\left(\lambda n \mapsto (\operatorname{a}\left(n\right): \mathbb{Z})\right) = 1 + 6 \cdot \operatorname{PowerSeries.X} + 22 \cdot \operatorname{PowerSeries.X}^{2} + 6 \cdot \operatorname{PowerSeries.X}^{3} + \operatorname{PowerSeries.X}^{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.result` (`✓ std3`). ∎

*Resolves.* `Problems/sloane298038` (proved) by `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sloane298038","declaration_gid":"D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

Write R(i,j,p,q) for TeaCoordinationSequence.residual, the nonnegative horizontal excess beyond −q≤i,j,i+j≤p. The potential at V(i,j) is 1+2R(i,j,1,0), at U(i,j) it is 2R(i,j,0,0), and at W(i,j) it is 2R(i+1,j+1,1,−1). The bound residual_le_iff gives the six coordinate inequalities for each of these three cases.

For each simplex type the proof takes the maximum of six affine functions of i and j and a baseline zero or one. The affine functions measure violations of the bounding lattice-polygon inequalities. Every simplex inclusion changes this integer potential by at most one. The potential is nonnegative and vanishes exactly at the root. At any other simplex, an incident simplex has potential smaller by one. For a vertex one can choose a containing face; for a face one can choose one of its vertices; for an edge one can choose an endpoint or a containing face. Strong induction constructs a walk attaining the potential. The lower bound for every walk then identifies it with graph distance.

The vertex and face slices reuse TeaCoordinationSequence.hexagon_mem and hexagon_card. For radius 2(k+1), the vertex slice is hexagon(k+1,k) and the upward-face slice is hexagon(k+1,k+1). At radius 2(k+1)+1 the vertex slice is hexagon(k+2,k+1), while the upward-face slice is unchanged. For either radius the downward-face slice maps bijectively to hexagon(k+2,k) by (i,j)↦(i+1,j+1). All endpoints are nonnegative, as required by the shared count 2|hexagon(p,q)|=p²+4pq+q²+3p+3q+2.

For the horizontal-edge slice, translate to natural coordinates 0≤u≤A, 0≤v≤B, l≤u+v and u+v+r≤A+B. The excluded corners contain l(l+1)/2 and r(r+1)/2 points by Finset.Nat.card_antidiagonal and Finset.sum_range_id_mul_two. They are disjoint under l+r≤A+B+1 and fit under l,r≤min(A+1,B+1). The vertical-edge slice has the same count by (i,j)↦(j,i); the diagonal-edge slice has the same count by (i,j)↦(i,−i−j). Summing the six slices gives 18k²+12k+1 points at distance at most 2k and 18k²+24k+7 at distance at most 2k+1, for every natural k. The distance lower bound directly uses the frozen VertexPositionRatioRefutation.potential_dist.

Successive ball differences give a(0)=1, a(2k+1)=12k+6 and a(2k+2)=24(k+1). Comparing coefficients of the displayed formal product proves the identity over the integers. PowerSeries.mk assigns the integer cast of a(n) to coefficient n; all exponents and coefficient indices are natural numbers. Subtraction of such indices in coefficient calculations is truncated natural subtraction. The series requires no analytic convergence assumption. OEIS A298038 revision 45 names the hexavalent-root sequence and attributes the rational generating-function conjecture to Colin Barker.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.Simplex`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.a`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.distance`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.graph`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.polygon`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.polygon_card`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.polygon_mem`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.result`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.root`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.shell_finite`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.support`
- Dependency: [D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation](../Combinatorics/PositionSets/VertexPositionRatioRefutation.md)
- Dependency: [D5/S3/StatisticalMechanics/TeaCoordinationSequence](TeaCoordinationSequence.md)
