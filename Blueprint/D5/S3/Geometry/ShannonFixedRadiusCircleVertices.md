# ShannonFixedRadiusCircleVertices

## Abstract

Shannon fixed-radius circle vertices have the three conjectured counts.

**Definition 1.1 (ShannonA374338.vertices).**

$$\forall (a b : \operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2)) , (\operatorname{ShannonA374338}.\operatorname{vertices} a b 0 = \{a , b\}) \land (\forall (n : \mathbb{N}) , \operatorname{ShannonA374338}.\operatorname{vertices} a b (n + 1) = \operatorname{ShannonA374338}.\operatorname{vertices} a b n \cup \{p : \operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2) \mid \exists (u : \operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2)) , u \in \operatorname{ShannonA374338}.\operatorname{vertices} a b n \land \exists (v : \operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2)) , v \in \operatorname{ShannonA374338}.\operatorname{vertices} a b n \land u \neq v \land p \in \operatorname{Metric}.\operatorname{sphere} u (\operatorname{dist} a b) \land p \in \operatorname{Metric}.\operatorname{sphere} v (\operatorname{dist} a b)\})$$

*Formalization.* `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.vertices` (`✓ std3`).

*Citation.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

OEIS A374338 revision 15, NAME (unpaginated), verbatim: “Start with two vertices and draw a circle around each whose radius is the distance between the vertices. The sequence gives the number of vertices constructed after n iterations of drawing circles with this same radius around every new vertex created from all circles' intersections. See the Comments.” Retained vertices are counted; iteration 2 has eight total vertices.

**Definition 1.2 (ShannonA374338.vertexCount).**

$$\forall (a b : \operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2)) (n : \mathbb{N}) , \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n = (\operatorname{ShannonA374338}.\operatorname{vertices} a b n) . \operatorname{ncard}$$

*Formalization.* `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.vertexCount` (`✓ std3`).

*Citation.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

OEIS A374338 revision 15, NAME (unpaginated), verbatim: “Start with two vertices and draw a circle around each whose radius is the distance between the vertices. The sequence gives the number of vertices constructed after n iterations of drawing circles with this same radius around every new vertex created from all circles' intersections. See the Comments.” Retained vertices are counted; iteration 2 has eight total vertices.

**Definition 1.3 (ShannonA374338.claim).**

$$\operatorname{ShannonA374338}.\operatorname{claim} \iff (\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , a \neq b \to (\forall (n k : \mathbb{N}) , n = 3 \cdot k + 1 \to \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n = \operatorname{Nat}.\operatorname{div} (3 \cdot n^{2} + 5 \cdot n + 4) 3) \land (\forall (n k : \mathbb{N}) , 1 \leq k \to n = 3 \cdot k \to \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n = \operatorname{Nat}.\operatorname{div} (3 \cdot n^{2} + 5 \cdot n) 3) \land (\forall (n k : \mathbb{N}) , 1 \leq k \to n = 3 \cdot k - 1 \to \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n = \operatorname{Nat}.\operatorname{div} (3 \cdot n^{2} + 5 \cdot n + 2) 3))$$

*Formalization.* `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.claim` (`✓ std3`).

*Citation.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

OEIS A374338 revision 15, FORMULA (unpaginated), verbatim: “Conjectured: If n = 3*k + 1, k >= 0, a(n) = (3*n^2 + 5*n + 4)/3. If n = 3*k, k >= 1, a(n) = (3*n^2 + 5*n)/3. If n = 3*k - 1, k >= 1, a(n) = (3*n^2 + 5*n + 2)/3.” The Euclidean starting points a and b are arbitrary and distinct; n and k are natural numbers. Nat.div denotes natural-number integer division.

**Definition 1.4 (HexCounts.square).**

$$\forall (L : \mathbb{N}) , \operatorname{HexCounts}.\operatorname{square} L = \operatorname{Finset}.\operatorname{filter} (\operatorname{fun} (p : \mathbb{N} \times \mathbb{N}) \mapsto \operatorname{Nat}.\operatorname{mod} p . 1 3 = \operatorname{Nat}.\operatorname{mod} p . 2 3) (\operatorname{Finset}.\operatorname{product} (\operatorname{Finset}.\operatorname{range} (L + 1)) (\operatorname{Finset}.\operatorname{range} (L + 1)))$$

*Formalization.* `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.square` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes HexCounts.square. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.5 (HexCounts.polygon).**

$$\forall (L n : \mathbb{N}) , \operatorname{HexCounts}.\operatorname{polygon} L n = \operatorname{Finset}.\operatorname{filter} (\operatorname{fun} (p : \mathbb{N} \times \mathbb{N}) \mapsto n < p . 1 + p . 2 \land p . 1 + p . 2 < 2 \cdot L - n) (\operatorname{HexCounts}.\operatorname{square} L)$$

*Formalization.* `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.polygon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes HexCounts.polygon. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.6 (HexCounts.polygon_zero).**

$$\forall (k : \mathbb{N}) , (\operatorname{HexCounts}.\operatorname{polygon} (2 \cdot (3 \cdot k) + 1) (3 \cdot k)) . \operatorname{card} = 9 \cdot k^{2} + 5 \cdot k$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.polygon_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexCounts.polygon_zero. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.7 (HexCounts.polygon_one).**

$$\forall (k : \mathbb{N}) , (\operatorname{HexCounts}.\operatorname{polygon} (2 \cdot (3 \cdot k + 1) + 1) (3 \cdot k + 1)) . \operatorname{card} = 9 \cdot k^{2} + 11 \cdot k + 4$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.polygon_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexCounts.polygon_one. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.8 (HexCounts.polygon_two).**

$$\forall (k : \mathbb{N}) , (\operatorname{HexCounts}.\operatorname{polygon} (2 \cdot (3 \cdot k + 2) + 1) (3 \cdot k + 2)) . \operatorname{card} = 9 \cdot k^{2} + 17 \cdot k + 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.polygon_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexCounts.polygon_two. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.9 (HexShapeCounts.inverse).**

$$\forall (n : \mathbb{N}) (p : \mathbb{N} \times \mathbb{N}) , \operatorname{HexShapeCounts}.\operatorname{inverse} n p = (\operatorname{Int}.\operatorname{ediv} (2 \cdot (p . 1 : \mathbb{Z}) + (p . 2 : \mathbb{Z})) 3 - (n : \mathbb{Z}) , \operatorname{Int}.\operatorname{ediv} ((p . 2 : \mathbb{Z}) - (p . 1 : \mathbb{Z})) 3)$$

*Formalization.* `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.inverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes HexShapeCounts.inverse. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.10 (HexShapeCounts.shape).**

$$\forall (m n : \mathbb{N}) , \operatorname{HexShapeCounts}.\operatorname{shape} m n = \operatorname{Finset}.\operatorname{image} (\operatorname{HexShapeCounts}.\operatorname{inverse} n) (\operatorname{HexCounts}.\operatorname{polygon} (m - 1 + 2 \cdot n) n)$$

*Formalization.* `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.shape` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes HexShapeCounts.shape. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.11 (HexShapeCounts.shape_card).**

$$\forall (m n : \mathbb{N}) , (\operatorname{HexShapeCounts}.\operatorname{shape} m n) . \operatorname{card} = (\operatorname{HexCounts}.\operatorname{polygon} (m - 1 + 2 \cdot n) n) . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.shape_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexShapeCounts.shape_card. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.12 (HexShapeCounts.grown_coe).**

$$\forall (m n : \mathbb{N}) , (m = 2 \lor m = 5) \to ((2 \leq n) \to (\operatorname{AxialGrowth}.\operatorname{grown} m n = (\operatorname{HexShapeCounts}.\operatorname{shape} m n : \operatorname{Set} (\mathbb{Z} \times \mathbb{Z}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.grown_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexShapeCounts.grown_coe. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.13 (HexShapeCounts.count_difference).**

$$\forall (n : \mathbb{N}) , (\operatorname{HexShapeCounts}.\operatorname{shape} 5 n) . \operatorname{card} = (\operatorname{HexShapeCounts}.\operatorname{shape} 2 n) . \operatorname{card} + 4 \cdot n + 7$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.count_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexShapeCounts.count_difference. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.14 (ShannonA374338.result).**

$$\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , a \neq b \to (\forall (n k : \mathbb{N}) , n = 3 \cdot k + 1 \to \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n = \operatorname{Nat}.\operatorname{div} (3 \cdot n^{2} + 5 \cdot n + 4) 3) \land (\forall (n k : \mathbb{N}) , 1 \leq k \to n = 3 \cdot k \to \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n = \operatorname{Nat}.\operatorname{div} (3 \cdot n^{2} + 5 \cdot n) 3) \land (\forall (n k : \mathbb{N}) , 1 \leq k \to n = 3 \cdot k - 1 \to \operatorname{ShannonA374338}.\operatorname{vertexCount} a b n = \operatorname{Nat}.\operatorname{div} (3 \cdot n^{2} + 5 \cdot n + 2) 3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

The three residue classes count all vertices for every pair of distinct Euclidean starting points.

## References

- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.claim`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.count_difference`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.grown_coe`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.inverse`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.polygon`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.polygon_one`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.polygon_two`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.polygon_zero`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.result`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.shape`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.shape_card`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.square`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.vertexCount`
- Truth anchor: `D5/S3/Geometry/ShannonFixedRadiusCircleVertices.vertices`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaLattice](../Arith/ModularForms/CubicThetaLattice.md)
- Dependency: [D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth](../StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.md)
