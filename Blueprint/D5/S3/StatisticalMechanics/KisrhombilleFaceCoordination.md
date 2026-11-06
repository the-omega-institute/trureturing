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

**Theorem 1.7 (Barker's generating-function identity).**

$$(1 - (\operatorname{PowerSeries.X}: \operatorname{PowerSeries}\left(\mathbb{Z}\right))^{2})^{2} \cdot \operatorname{PowerSeries.mk}\left(\lambda n \mapsto (\operatorname{a}\left(n\right): \mathbb{Z})\right) = 1 + 6 \cdot \operatorname{PowerSeries.X} + 22 \cdot \operatorname{PowerSeries.X}^{2} + 6 \cdot \operatorname{PowerSeries.X}^{3} + \operatorname{PowerSeries.X}^{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298038: coordination sequence of Dual(4.6.12) at a hexavalent node*. URL: <https://oeis.org/A298038>.

*Commentary.*

For each simplex type the proof takes the maximum of six affine functions of i and j and a baseline zero or one. The affine functions measure violations of the bounding lattice-polygon inequalities. Every simplex inclusion changes this integer potential by at most one. The potential is nonnegative and vanishes exactly at the root. At any other simplex, an incident simplex has potential smaller by one. For a vertex one can choose a containing face; for a face one can choose one of its vertices; for an edge one can choose an endpoint or a containing face. Strong induction constructs a walk attaining the potential. The lower bound for every walk then identifies it with graph distance.

A coordinate slice of a ball is a rectangle cut by two diagonal inequalities. Translate it to natural coordinates 0≤u≤A, 0≤v≤B, l≤u+v and u+v+r≤A+B. The excluded corners contain l(l+1)/2 and r(r+1)/2 points. They are disjoint under l+r≤A+B+1, and both fit in the rectangle under l,r≤min(A+1,B+1). Counting the antidiagonals proves these triangular counts. The sum over all six simplex types gives 18k²+12k+1 points at distance at most 2k, and 18k²+24k+7 points at distance at most 2k+1, for every natural k.

Successive ball differences give a(0)=1, a(2k+1)=12k+6 and a(2k+2)=24(k+1). Comparing coefficients of the displayed formal product proves the identity over the integers. PowerSeries.mk assigns the integer cast of a(n) to coefficient n; all exponents and coefficient indices are natural numbers. Subtraction of such indices in coefficient calculations is truncated natural subtraction. The series requires no analytic convergence assumption. OEIS A298038 revision 45 names the hexavalent-root sequence and attributes the rational generating-function conjecture to Colin Barker.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.Simplex`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.a`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.distance`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.graph`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.result`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.root`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination.support`
- Dependency: [D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation](../Combinatorics/PositionSets/VertexPositionRatioRefutation.md)
