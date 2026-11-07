# Edge-rooted kisrhombille coordination

## Abstract

Barker's formal generating-function identity for the tetravalent root of the kisrhombille tiling.

Use KisrhombilleFaceCoordination.Simplex, support and graph. A simplex is (t,(i,j)), with t in Fin 6 and integer coordinates i,j. Types zero through five are a vertex V, horizontal edge H, vertical edge B, diagonal edge D, upward face U and downward face W. Two distinct simplices are adjacent exactly when their finite vertex supports are comparable by inclusion. The triangular lattice has difference vectors ±(1,0), ±(0,1), ±(1,−1). In particular, vertices are adjacent to containing faces as well as containing edges. U(i,j) has vertices (i,j),(i+1,j),(i,j+1); W(i,j) has vertices (i+1,j),(i,j+1),(i+1,j+1).

**Definition 1.1 (The specified edge).**

$$root = (1, (0, 0))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination.root` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298040: coordination sequence of Dual(4.6.12) at a tetravalent node*. URL: <https://oeis.org/A298040>.

*Commentary.*

This is H(0,0), whose support is {(0,0),(1,0)}. Its four neighbors are V(0,0), V(1,0), U(0,0) and W(0,−1).

**Definition 1.2 (Minimum walk length).**

$$\forall s: Simplex, (\operatorname{distance}\left(s\right) = \operatorname{SimpleGraph.dist}\left(graph, root, s\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination.distance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298040: coordination sequence of Dual(4.6.12) at a tetravalent node*. URL: <https://oeis.org/A298040>.

*Commentary.*

Distance is the genuine shortest-walk distance in the shared inclusion graph. The proof constructs a walk from this root to every simplex.

**Definition 1.3 (Finite distance shells).**

$$\forall n: \mathbb{N}, (\operatorname{a}\left(n\right) = \operatorname{Set.ncard}\left(\{s: Simplex \mid \operatorname{distance}\left(s\right) = n\}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298040: coordination sequence of Dual(4.6.12) at a tetravalent node*. URL: <https://oeis.org/A298040>.

*Commentary.*

Set.ncard gives the natural cardinality. Each shell is finite: the face-root distance is at most the edge-root distance plus one, so this shell lies in a finite union of the finite face-root shells. The radius-zero shell contains exactly the root.

**Theorem 1.4 (Barker's generating-function identity).**

$$(1 - (\operatorname{PowerSeries.X}: \operatorname{PowerSeries}\left(\mathbb{Z}\right))^{2})^{2} \cdot \operatorname{PowerSeries.mk}\left(\lambda n \mapsto (\operatorname{a}\left(n\right): \mathbb{Z})\right) = 1 + 4 \cdot \operatorname{PowerSeries.X} + 18 \cdot \operatorname{PowerSeries.X}^{2} + 16 \cdot \operatorname{PowerSeries.X}^{3} + \operatorname{PowerSeries.X}^{4} - 4 \cdot \operatorname{PowerSeries.X}^{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane, Colin Barker (2018). *OEIS A298040: coordination sequence of Dual(4.6.12) at a tetravalent node*. URL: <https://oeis.org/A298040>.

*Commentary.*

For a vertex at (i,j), take the maximum of 1, 1−2i, 2i−1, −2j, 2j, 1−2(i+j), 2(i+j)−1. For U(i,j), take the maximum of 1, −2i, 2i, −2j−1, 2j+1, −2(i+j), 2(i+j). For W(i,j), replace the last two terms by −2(i+j)−2 and 2(i+j)+2. An edge other than the root has potential one plus the minimum potential of its two endpoints and two containing faces; the root has potential zero. Inclusion changes potential by at most one. Every positive-potential simplex has an incident simplex with potential one smaller. Induction builds a walk attaining this potential, and VertexPositionRatioRefutation.potential_dist gives the matching lower bound.

At radius 2k+1 the six coordinate-slice counts, in type order, are 3k²+5k+2, 3k²+3k+1, 3k²+5k, 3k²+5k, 3k²+4k+1, 3k²+4k+1. At radius 2k+2 they are 3k²+7k+4, 3k²+9k+3, 3k²+7k+4, 3k²+7k+4, 3k²+8k+5, 3k²+8k+5. These formulas hold for every natural k. The horizontal-edge slice at odd radius uses TeaCoordinationSequence.hexagon and its count. Other polygon counts use KisrhombilleFaceCoordination.polygon_mem and polygon_card. The even horizontal-edge slice and positive odd vertical-edge slice each adjoin two disjoint boundary rows to a polygon. Reflection gives equal vertical and diagonal counts, and equal upward and downward face counts.

Summing gives ball sizes 18k²+26k+5 at radius 2k+1 and 18k²+46k+25 at radius 2k+2. Successive differences give a(0)=1, a(1)=4, a(2k+2)=20(k+1) and a(2k+3)=16k+24. Coefficient comparison proves the displayed identity. PowerSeries.mk assigns coefficient n the integer cast of a(n); indices and powers are natural numbers, with truncated subtraction of indices. X denotes the formal indeterminate, and the cast on its first occurrence specifies PowerSeries ℤ. No convergence assumption is needed. OEIS A298040 revision 36 names the tetravalent-root sequence and attributes the rational generating-function conjecture to Colin Barker.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination.a`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination.distance`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination.result`
- Truth anchor: `D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination.root`
- Dependency: [D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation](../Combinatorics/PositionSets/VertexPositionRatioRefutation.md)
- Dependency: [D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination](KisrhombilleFaceCoordination.md)
- Dependency: [D5/S3/StatisticalMechanics/TeaCoordinationSequence](TeaCoordinationSequence.md)
