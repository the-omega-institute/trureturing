# TriangularTwoNeighborGrowth

## Abstract

Exact expanding hexagons and Euclidean fixed-radius lattice geometry.

**Definition 1.1 (MarkeyA400701.directions).**

$$\operatorname{MarkeyA400701}.\operatorname{directions} = \{(1 , 0) , (0 , 1) , (1 , - 1) , (- 1 , 0) , (0 , - 1) , (- 1 , 1)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.directions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes MarkeyA400701.directions. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.2 (MarkeyA400701.coordinates).**

$$\forall (n : \mathbb{N}) (p : \operatorname{Fin} (2 \cdot n + 7) \times \operatorname{Fin} (2 \cdot n + 3)) , \operatorname{MarkeyA400701}.\operatorname{coordinates} n p = (((p . 1 . \operatorname{val} : \mathbb{Z}) - (n : \mathbb{Z}) - 1) , ((p . 2 . \operatorname{val} : \mathbb{Z}) - (n : \mathbb{Z}) - 1))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes MarkeyA400701.coordinates. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.3 (MarkeyA400701.windowGraph).**

$$\forall (n : \mathbb{N}) , \operatorname{MarkeyA400701}.\operatorname{windowGraph} n = \operatorname{SimpleGraph}.\operatorname{fromRel} (\operatorname{fun} (p q : \operatorname{Fin} (2 \cdot n + 7) \times \operatorname{Fin} (2 \cdot n + 3)) \mapsto \operatorname{MarkeyA400701}.\operatorname{coordinates} n q - \operatorname{MarkeyA400701}.\operatorname{coordinates} n p \in \operatorname{MarkeyA400701}.\operatorname{directions})$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.windowGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes MarkeyA400701.windowGraph. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.4 (MarkeyA400701.seed).**

$$\forall (n : \mathbb{N}) , \operatorname{MarkeyA400701}.\operatorname{seed} n = \operatorname{Finset}.\operatorname{filter} (\operatorname{fun} (p : \operatorname{Fin} (2 \cdot n + 7) \times \operatorname{Fin} (2 \cdot n + 3)) \mapsto 0 \leq (\operatorname{MarkeyA400701}.\operatorname{coordinates} n p) . 1 \land (\operatorname{MarkeyA400701}.\operatorname{coordinates} n p) . 1 \leq 4 \land (\operatorname{MarkeyA400701}.\operatorname{coordinates} n p) . 2 = 0) \operatorname{Finset}.\operatorname{univ}$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.seed` (`✓ std3`).

*Citation.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

OEIS A400701 revision 30, NAME (unpaginated), verbatim: “Start with a set of five adjacent collinear points in a hexagonal lattice. Every iteration, add to the set the points in the lattice which are adjacent to at least two points already in the set. This sequence gives the number of points in the set after n iterations.” FORMULA, verbatim: “Conjectured: For n > 1: a(n) = A374338(n) + 4*n + 7.” The lattice has six unit directions. Both counts use the same natural iteration index.

**Definition 1.5 (MarkeyA400701.latticeCount).**

$$\forall (n : \mathbb{N}) , \operatorname{MarkeyA400701}.\operatorname{latticeCount} n = (\operatorname{Function}.\operatorname{iterate} (\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Percolation}.\operatorname{DirectProductCyclePathBootstrap}.\operatorname{step} (\operatorname{MarkeyA400701}.\operatorname{windowGraph} n) 2) n (\operatorname{MarkeyA400701}.\operatorname{seed} n)) . \operatorname{card}$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.latticeCount` (`✓ std3`).

*Citation.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

OEIS A400701 revision 30, NAME (unpaginated), verbatim: “Start with a set of five adjacent collinear points in a hexagonal lattice. Every iteration, add to the set the points in the lattice which are adjacent to at least two points already in the set. This sequence gives the number of points in the set after n iterations.” FORMULA, verbatim: “Conjectured: For n > 1: a(n) = A374338(n) + 4*n + 7.” The lattice has six unit directions. Both counts use the same natural iteration index.

**Definition 1.6 (HexGrowth.Hex).**

$$\forall (A L : \mathbb{Z}) (p : \mathbb{Z} \times \mathbb{Z}) , \operatorname{HexGrowth}.\operatorname{Hex} A L p \iff 0 \leq p . 1 \land p . 1 \leq L \land 0 \leq p . 2 \land p . 2 \leq L \land A \leq p . 1 + p . 2 \land p . 1 + p . 2 \leq 2 \cdot L - A$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.Hex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes HexGrowth.Hex. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.7 (AxialGrowth.transform).**

$$\forall (n : \mathbb{N}) (p : \mathbb{Z} \times \mathbb{Z}) , \operatorname{AxialGrowth}.\operatorname{transform} n p = (p . 1 - p . 2 + (n : \mathbb{Z}) , p . 1 + 2 \cdot p . 2 + (n : \mathbb{Z}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.transform` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes AxialGrowth.transform. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.8 (AxialGrowth.H).**

$$\forall (m n : \mathbb{N}) , \operatorname{AxialGrowth}.\operatorname{H} m n = \{p : \mathbb{Z} \times \mathbb{Z} \mid \operatorname{HexGrowth}.\operatorname{Hex} ((n : \mathbb{Z}) + 1) ((m : \mathbb{Z}) - 1 + 2 \cdot (n : \mathbb{Z})) (\operatorname{AxialGrowth}.\operatorname{transform} n p)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes AxialGrowth.H. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.9 (AxialGrowth.Two).**

$$\forall (S : \operatorname{Set} (\mathbb{Z} \times \mathbb{Z})) (p : \mathbb{Z} \times \mathbb{Z}) , \operatorname{AxialGrowth}.\operatorname{Two} S p \iff \exists (d : \mathbb{Z} \times \mathbb{Z}) , d \in \operatorname{MarkeyA400701}.\operatorname{directions} \land \exists (e : \mathbb{Z} \times \mathbb{Z}) , e \in \operatorname{MarkeyA400701}.\operatorname{directions} \land d \neq e \land p + d \in S \land p + e \in S$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.Two` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes AxialGrowth.Two. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.10 (AxialGrowth.next).**

$$\forall (S : \operatorname{Set} (\mathbb{Z} \times \mathbb{Z})) , \operatorname{AxialGrowth}.\operatorname{next} S = S \cup \{p : \mathbb{Z} \times \mathbb{Z} \mid \operatorname{AxialGrowth}.\operatorname{Two} S p\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.next` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes AxialGrowth.next. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.11 (AxialGrowth.initial).**

$$\forall (m : \mathbb{N}) , \operatorname{AxialGrowth}.\operatorname{initial} m = \{p : \mathbb{Z} \times \mathbb{Z} \mid 0 \leq p . 1 \land p . 1 < (m : \mathbb{Z}) \land p . 2 = 0\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes AxialGrowth.initial. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.12 (AxialGrowth.grown).**

$$\forall (m : \mathbb{N}) , (\operatorname{AxialGrowth}.\operatorname{grown} m 0 = \operatorname{AxialGrowth}.\operatorname{initial} m) \land (\forall (n : \mathbb{N}) , \operatorname{AxialGrowth}.\operatorname{grown} m (n + 1) = \operatorname{AxialGrowth}.\operatorname{next} (\operatorname{AxialGrowth}.\operatorname{grown} m n))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.grown` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes AxialGrowth.grown. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.13 (AxialGrowth.first).**

$$\forall (m : \mathbb{N}) , \operatorname{AxialGrowth}.\operatorname{first} m = \{p : \mathbb{Z} \times \mathbb{Z} \mid (p . 2 = 0 \land 0 \leq p . 1 \land p . 1 < (m : \mathbb{Z})) \lor (p . 2 = 1 \land 0 \leq p . 1 \land p . 1 < (m : \mathbb{Z}) - 1) \lor (p . 2 = - 1 \land 1 \leq p . 1 \land p . 1 < (m : \mathbb{Z}))\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.first` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes AxialGrowth.first. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.14 (AxialGrowth.first_step).**

$$\forall (m : \mathbb{N}) , \operatorname{AxialGrowth}.\operatorname{grown} m 1 = \operatorname{AxialGrowth}.\operatorname{first} m$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.first_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes AxialGrowth.first_step. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.15 (AxialGrowth.exact_shape).**

$$\forall (m n : \mathbb{N}) , (m = 2 \lor m = 5) \to ((2 \leq n) \to (\operatorname{AxialGrowth}.\operatorname{grown} m n = \operatorname{AxialGrowth}.\operatorname{H} m n))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.exact_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes AxialGrowth.exact_shape. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.16 (HexEmbedding.axial).**

$$\forall (x y : \mathbb{R}) , \operatorname{HexEmbedding}.\operatorname{axial} x y = ((x + y / 2 : \mathbb{R}) : \mathbb{C}) + (((\operatorname{Real}.\operatorname{sqrt} 3 \cdot y / 2 : \mathbb{R}) : \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I})$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.axial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes HexEmbedding.axial. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.17 (HexEmbedding.frame).**

$$\forall (a b : \operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2)) (z : \mathbb{C}) , \operatorname{HexEmbedding}.\operatorname{frame} a b z = \operatorname{Complex}.\operatorname{orthonormalBasisOneI}.\operatorname{repr} (\operatorname{AffineMap}.\operatorname{lineMap} (\operatorname{Complex}.\operatorname{orthonormalBasisOneI}.\operatorname{repr}.\operatorname{symm} a) (\operatorname{Complex}.\operatorname{orthonormalBasisOneI}.\operatorname{repr}.\operatorname{symm} b) z)$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.frame` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes HexEmbedding.frame. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Definition 1.18 (HexEmbedding.embed).**

$$\forall (a b : \operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2)) (p : \mathbb{Z} \times \mathbb{Z}) , \operatorname{HexEmbedding}.\operatorname{embed} a b p = \operatorname{HexEmbedding}.\operatorname{frame} a b (\operatorname{HexEmbedding}.\operatorname{axial} (p . 1 : \mathbb{R}) (p . 2 : \mathbb{R}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.embed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This expression describes HexEmbedding.embed. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.19 (HexEmbedding.frame_zero).**

$$\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , \operatorname{HexEmbedding}.\operatorname{frame} a b 0 = a$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.frame_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexEmbedding.frame_zero. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.20 (HexEmbedding.frame_one).**

$$\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , \operatorname{HexEmbedding}.\operatorname{frame} a b 1 = b$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.frame_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexEmbedding.frame_one. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.21 (HexEmbedding.embed_injective).**

$$\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , (a \neq b) \to (\operatorname{Function}.\operatorname{Injective} (\operatorname{HexEmbedding}.\operatorname{embed} a b))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.embed_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes HexEmbedding.embed_injective. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.22 (CircleGrowth.directions_neg).**

$$\forall (p : \mathbb{Z} \times \mathbb{Z}) , - p \in \operatorname{MarkeyA400701}.\operatorname{directions} \iff p \in \operatorname{MarkeyA400701}.\operatorname{directions}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.directions_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes CircleGrowth.directions_neg. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.23 (CircleGrowth.embed_adjacent).**

$$\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , (a \neq b) \to (\forall (u v : \mathbb{Z} \times \mathbb{Z}) , (u - v \in \operatorname{MarkeyA400701}.\operatorname{directions}) \to (\operatorname{dist} (\operatorname{HexEmbedding}.\operatorname{embed} a b u) (\operatorname{HexEmbedding}.\operatorname{embed} a b v) = \operatorname{dist} a b))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.embed_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes CircleGrowth.embed_adjacent. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

**Theorem 1.24 (CircleGrowth.intersection_lattice).**

$$\forall (a b : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , (a \neq b) \to (\forall (u v : \mathbb{Z} \times \mathbb{Z}) , (u \neq v) \to (\forall (p : (\operatorname{EuclideanSpace} \mathbb{R} (\operatorname{Fin} 2))) , (\operatorname{dist} p (\operatorname{HexEmbedding}.\operatorname{embed} a b u) = \operatorname{dist} a b) \to ((\operatorname{dist} p (\operatorname{HexEmbedding}.\operatorname{embed} a b v) = \operatorname{dist} a b) \to (\exists w : \mathbb{Z} \times \mathbb{Z} , \operatorname{HexEmbedding}.\operatorname{embed} a b w = p \land w - u \in \operatorname{MarkeyA400701}.\operatorname{directions} \land w - v \in \operatorname{MarkeyA400701}.\operatorname{directions}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.intersection_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott R. Shannon; Aidan Markey (2024). *OEIS A374338 (2024) fixed-radius circle vertices and A400701 (2026) five-site triangular growth*. URL: <https://oeis.org/A374338>.

*Commentary.*

This identity describes CircleGrowth.intersection_lattice. Integer division on natural and integer coordinates is written Nat.div and Int.ediv, respectively.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.H`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.Hex`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.Two`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.axial`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.coordinates`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.directions`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.directions_neg`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.embed`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.embed_adjacent`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.embed_injective`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.exact_shape`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.first`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.first_step`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.frame`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.frame_one`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.frame_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.grown`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.intersection_lattice`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.latticeCount`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.next`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.seed`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.transform`
- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/TriangularTwoNeighborGrowth.windowGraph`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaLattice](../../Arith/ModularForms/CubicThetaLattice.md)
- Dependency: [D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap](DirectProductCyclePathBootstrap.md)
