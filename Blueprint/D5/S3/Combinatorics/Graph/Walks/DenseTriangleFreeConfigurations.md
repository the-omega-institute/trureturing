# DenseTriangleFreeConfigurations

## Abstract

Finite graph structure, degree counting, and perfect matchings.

**Definition 1.1 (A3Edges).**

$$(\operatorname{A3Edges}: \operatorname{Finset} (\operatorname{Fin} 8 \times \operatorname{Fin} 8)) = \ \{(0 , 3) , (0 , 4) , (0 , 5) , (1 , 4) , (1 , 5) , (1 , 6) , (2 , 5) , (2 , 6) , (2 , 7) , (3 , 0) , (3 , 6) , (3 , 7) , (4 , 0) , (4 , 1) , (4 , 7) , (5 , 0) , (5 , 1) , (5 , 2) , (6 , 1) , (6 , 2) , (6 , 3) , (7 , 2) , (7 , 3) , (7 , 4)\ \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.A3Edges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The listed ordered pairs give both orientations of the edges of the eight-vertex Andrásfai graph.

**Definition 1.2 (MycEdges).**

$$(\operatorname{MycEdges}: \operatorname{Finset} (\operatorname{Fin} 11 \times \operatorname{Fin} 11)) = \ \{(0 , 1) , (0 , 4) , (0 , 6) , (0 , 9) , (1 , 0) , (1 , 2) , (1 , 5) , (1 , 7) , (2 , 1) , (2 , 3) , (2 , 6) , (2 , 8) , (3 , 2) , (3 , 4) , (3 , 7) , (3 , 9) , (4 , 0) , (4 , 3) , (4 , 5) , (4 , 8) , (5 , 1) , (5 , 4) , (5 , 10) , (6 , 0) , (6 , 2) , (6 , 10) , (7 , 1) , (7 , 3) , (7 , 10) , (8 , 2) , (8 , 4) , (8 , 10) , (9 , 0) , (9 , 3) , (9 , 10) , (10 , 5) , (10 , 6) , (10 , 7) , (10 , 8) , (10 , 9)\ \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.MycEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The edge list specifies the eleven-vertex Mycielski graph built from a five-cycle.

**Definition 1.3 (A3).**

$$\forall (i j: \operatorname{Fin} 8), (\operatorname{A3} . \operatorname{Adj} i j)\iff((i , j) \in \operatorname{A3Edges})$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.A3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Adjacency is membership in the displayed Andrásfai edge list.

**Definition 1.4 (Myc).**

$$\forall (i j: \operatorname{Fin} 11), (\operatorname{Myc} . \operatorname{Adj} i j)\iff((i , j) \in \operatorname{MycEdges})$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.Myc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Adjacency is membership in the displayed Mycielski edge list.

**Theorem 1.5 (pentagon edge iff).**

$$\forall (i j: \operatorname{Fin} 5), ((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{comap} (fun (t: \operatorname{Fin} 5)\mapsto 3 \cdot t)) . \operatorname{Adj} i j \iff ((j = i + 2)\lor(j = i + 3))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.pentagon_edge_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Multiplication by three identifies the standard five-cycle adjacency with steps two and three.

**Definition 1.6 (Pentagon).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), \forall (p: (\operatorname{Fin} 5)\to(V)), (\operatorname{Pentagon} G p)\iff((\forall (i j: \operatorname{Fin} 5), ((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{comap} (fun (t: \operatorname{Fin} 5)\mapsto 3 \cdot t)) . \operatorname{Adj} i j \to G . \operatorname{Adj} (p i) (p j)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.Pentagon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

A map from the five-cycle preserves every adjacency in its step-two cyclic ordering.

**Definition 1.7 (Twin).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), \forall (p: (\operatorname{Fin} 5)\to(V)), \forall (x: V), \forall (i: \operatorname{Fin} 5), (\operatorname{Twin} G p x i)\iff((\forall (j: \operatorname{Fin} 5), (G . \operatorname{Adj} x (p j))\iff(((\operatorname{SimpleGraph} . \operatorname{cycleGraph} 5) . \operatorname{comap} (fun (t: \operatorname{Fin} 5)\mapsto 3 \cdot t)) . \operatorname{Adj} i j)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.Twin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

A vertex has precisely the same neighbors on the chosen pentagon as its indexed pentagon vertex.

**Definition 1.8 (NoHex).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), (\operatorname{NoHex} G)\iff((\forall (a b c d e f: V), (G . \operatorname{Adj} a b)\to((G . \operatorname{Adj} b c)\to((G . \operatorname{Adj} c d)\to((G . \operatorname{Adj} d e)\to((G . \operatorname{Adj} e f)\to((G . \operatorname{Adj} f a)\to(((G . \operatorname{Adj} a d)\lor((G . \operatorname{Adj} b e)\lor(G . \operatorname{Adj} c f)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.NoHex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Every closed six-edge walk has at least one of the three opposite diagonals.

**Theorem 1.9 (twin of two).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), (\forall (a b c: V), (G . \operatorname{Adj} a b)\to((G . \operatorname{Adj} b c)\to(\neg G . \operatorname{Adj} a c))) \to (\forall (p: (\operatorname{Fin} 5)\to(V)), ((\operatorname{Pentagon} G p))\to((\forall (x: V), \forall (i: \operatorname{Fin} 5), ((G . \operatorname{Adj} x (p (i + 2))))\to((((G . \operatorname{Adj} x (p (i + 3))))\to((\operatorname{Twin} G p x i)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.twin_of_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Triangle-freeness determines the entire pentagon neighborhood from the two required adjacent positions.

**Theorem 1.10 (twin edge zero two).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), (\forall (a b c: V), (G . \operatorname{Adj} a b)\to((G . \operatorname{Adj} b c)\to(\neg G . \operatorname{Adj} a c))) \to (((\operatorname{NoHex} G))\to(((\forall (a b: V), (\neg G . \operatorname{Adj} a b)\to(\exists (r: V), (G . \operatorname{Adj} a r)\land(G . \operatorname{Adj} b r))) \to (((\neg \operatorname{Nonempty} (SimpleGraph.Hom\left(\operatorname{A3}, G\right))))\to((\forall (p: (\operatorname{Fin} 5)\to(V)), ((\operatorname{Pentagon} G p))\to((\forall (x: V), \forall (y: V), ((\operatorname{Twin} G p x 0))\to((((\operatorname{Twin} G p y 2))\to((G . \operatorname{Adj} x y))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.twin_edge_zero_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

In a triangle-free graph with no induced hexagon, a common neighbor for every nonedge, and no homomorphism from A3, twins at pentagon positions zero and two are adjacent.

**Theorem 1.11 (triangle free of clique free).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], ((G . \operatorname{CliqueFree} 3))\to((\forall (a: V), \forall (b: V), \forall (c: V), ((G . \operatorname{Adj} a b))\to((((G . \operatorname{Adj} b c))\to((\neg G . \operatorname{Adj} a c))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.triangle_free_of_clique_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

A graph with no three-vertex clique has no triangle: two consecutive edges rule out the edge joining their other endpoints.

**Theorem 1.12 (no a3).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], (\forall (a b c: V), (G . \operatorname{Adj} a b)\to((G . \operatorname{Adj} b c)\to(\neg G . \operatorname{Adj} a c))) \to (((3 \cdot \operatorname{Fintype} . \operatorname{card} V < 8 \cdot G . \operatorname{minDegree}))\to((\neg \operatorname{Nonempty} (SimpleGraph.Hom\left(\operatorname{A3}, G\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.no_a3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The strict three-eighths degree bound excludes a homomorphism from the eight-vertex Andrásfai graph.

**Theorem 1.13 (no myc).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], (\forall (a b c: V), (G . \operatorname{Adj} a b)\to((G . \operatorname{Adj} b c)\to(\neg G . \operatorname{Adj} a c))) \to (((3 \cdot \operatorname{Fintype} . \operatorname{card} V < 8 \cdot G . \operatorname{minDegree}))\to((\neg \operatorname{Nonempty} (SimpleGraph.Hom\left(\operatorname{Myc}, G\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.no_myc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The Mycielski weighted independent-set bound excludes a homomorphism into a graph above the strict three-eighths density threshold.

**Theorem 1.14 (d2).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], ((3 \cdot \operatorname{Fintype} . \operatorname{card} V < 8 \cdot G . \operatorname{minDegree}))\to((\forall (f: (\operatorname{Fin} 6)\to(V)), \exists (v: V), 3 \leq (\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (fun (i: \operatorname{Fin} 6)\mapsto G . \operatorname{Adj} v (f i))) . \operatorname{card}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.d2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Double counting the adjacencies to six indexed positions supplies a common neighbor of at least three positions.

**Theorem 1.15 (d3).**

$$\forall (V: \operatorname{Type}), \forall [\operatorname{Fintype} V], \forall [\operatorname{DecidableEq} V], \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], ((3 \cdot \operatorname{Fintype} . \operatorname{card} V < 8 \cdot G . \operatorname{minDegree}))\to((\forall (f: (\operatorname{Fin} 9)\to(V)), \exists (v: V), 4 \leq (\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (fun (i: \operatorname{Fin} 9)\mapsto G . \operatorname{Adj} v (f i))) . \operatorname{card}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.d3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Double counting the adjacencies to nine indexed positions supplies a common neighbor of at least four positions.

**Definition 1.16 (D2).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], (\operatorname{D2} G)\iff((\forall (f: (\operatorname{Fin} 6)\to(V)), \exists (x: V), 3 \leq (\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (fun (i: \operatorname{Fin} 6)\mapsto G . \operatorname{Adj} x (f i))) . \operatorname{card}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.D2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Among any six indexed positions, one vertex is adjacent to at least three positions.

**Definition 1.17 (D3).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], (\operatorname{D3} G)\iff((\forall (f: (\operatorname{Fin} 9)\to(V)), \exists (x: V), 4 \leq (\operatorname{Finset} . \operatorname{univ} . \operatorname{filter} (fun (i: \operatorname{Fin} 9)\mapsto G . \operatorname{Adj} x (f i))) . \operatorname{card}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.D3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

Among any nine indexed positions, one vertex is adjacent to at least four positions.

**Theorem 1.18 (no hexagon).**

$$\forall (V: \operatorname{Type}), \forall (G: \operatorname{SimpleGraph} V), \forall [\operatorname{DecidableRel} G . \operatorname{Adj}], (\forall (a b c: V), (G . \operatorname{Adj} a b)\to((G . \operatorname{Adj} b c)\to(\neg G . \operatorname{Adj} a c))) \to (((\operatorname{D2} G))\to((((\operatorname{D3} G))\to(((\forall (a b: V), (\neg G . \operatorname{Adj} a b)\to(\exists (r: V), (G . \operatorname{Adj} a r)\land(G . \operatorname{Adj} b r))) \to (((\neg \operatorname{Nonempty} (SimpleGraph.Hom\left(\operatorname{Myc}, G\right))))\to((\operatorname{NoHex} G))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.no_hexagon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Ahanjideh; T. Ekim; M. A. Yıldız (2022). *Maximum size of a triangle-free graph with bounded maximum degree and matching number*. DOI: [10.1007/s10878-024-01123-z](https://doi.org/10.1007/s10878-024-01123-z). URL: <https://arxiv.org/abs/2207.02271v1>.

*Commentary.*

The six- and nine-position common-neighbor properties, together with a common neighbor for each nonadjacent pair and the excluded Mycielski homomorphism, force a diagonal in every closed hexagon.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.A3`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.A3Edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.D2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.D3`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.Myc`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.MycEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.NoHex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.Pentagon`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.Twin`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.d2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.d3`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.no_a3`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.no_hexagon`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.no_myc`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.pentagon_edge_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.triangle_free_of_clique_free`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.twin_edge_zero_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/DenseTriangleFreeConfigurations.twin_of_two`
