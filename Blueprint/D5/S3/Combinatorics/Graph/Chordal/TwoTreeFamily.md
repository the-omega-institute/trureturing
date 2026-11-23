# Circulations of recursive two-trees

## Abstract

Signed edge balances determine the triangle coordinates of a circulation.

Orient the core triangle cyclically. Each inserted vertex lies between the source and target of its parent edge. Orient the two new edges along that path and retain the old orientation on the parent.

**Theorem 1.1 (Coordinates of triangle chains).**

$$\forall ell \in \operatorname{Universe}\left(\right),\; \forall R \in \operatorname{Type}\left(ell\right),\; [\operatorname{CommRing}\left(R\right)] , \forall d \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{TwoTreeTriangles}\left(d\right),\; \operatorname{twoTreeCirculationCoordinates}\left(R, d, \operatorname{twoTreeTriangleChain}\left(R, d, i\right)\right) = \operatorname{single}\left(i, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.twoTree_triangle_chain_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each fresh vertex, conservation makes the two child coefficients equal. Subtracting that coefficient times the insertion triangle clears the two children and adds the coefficient to their parent edge. This reduces to a circulation on the preceding round. On the core, the three coefficients are equal. The reverse construction is linear and restores the original circulation.

**Theorem 1.2 (Triangles of the graph).**

$$\forall d \in \operatorname{Nat}\left(\right),\; (\forall a \in \operatorname{TwoTreeV}\left(d\right),\; \forall b \in \operatorname{TwoTreeV}\left(d\right),\; \forall c \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), a, b\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), b, c\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), a, c\right)) \Rightarrow (\exists i \in \operatorname{TwoTreeTriangles}\left(d\right),\; \operatorname{twoTreeTriangleVertices}\left(d, i\right) = \left\{a, b, c\right\})))) \land (\forall i \in \operatorname{TwoTreeTriangles}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), \operatorname{fst}\left(\operatorname{twoTreeOrientedTriangle}\left(d, i\right)\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{twoTreeOrientedTriangle}\left(d, i\right)\right)\right)\right)) \land ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{twoTreeOrientedTriangle}\left(d, i\right)\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(\operatorname{twoTreeOrientedTriangle}\left(d, i\right)\right)\right)\right)) \land (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), \operatorname{snd}\left(\operatorname{snd}\left(\operatorname{twoTreeOrientedTriangle}\left(d, i\right)\right)\right), \operatorname{fst}\left(\operatorname{twoTreeOrientedTriangle}\left(d, i\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.twoTree_triangles_classify` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A triangle either lies in the preceding graph or contains a single newest vertex and its two parents.

**Theorem 1.3 (Triangle-filling norm).**

$$\forall d \in \operatorname{Nat}\left(\right),\; \forall z \in \operatorname{TwoTreeCirculation}\left(\operatorname{Real}\left(\right), d\right),\; \operatorname{twoTreeFillingNorm}\left(d, z\right) = \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{twoTreeCirculationCoordinates}\left(\operatorname{Real}\left(\right), d, z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.twoTree_filling_norm_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triangle chains are an integral basis and remain a basis with real coefficients. Every filling has the same coefficient vector, so its length is the sum of the absolute values of those coordinates.

**Theorem 1.4 (Evaluation of triangle gains).**

$$\forall ell \in \operatorname{Universe}\left(\right),\; \forall vee \in \operatorname{Universe}\left(\right),\; \forall R \in \operatorname{Type}\left(ell\right),\; \forall E \in \operatorname{Type}\left(vee\right),\; [\operatorname{CommRing}\left(R\right)] [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(R, E\right)] , \forall d \in \operatorname{Nat}\left(\right),\; \forall tau \in \operatorname{TwoTreeTriangles}\left(d\right) \to E,\; \forall z \in \operatorname{TwoTreeCirculation}\left(R, d\right),\; \sum_{j : \operatorname{TwoTreeEdges}\left(d\right)} (\operatorname{smul}\left(\operatorname{val}\left(z, j\right), \operatorname{twoTreeTriangleGain}\left(d, tau, \operatorname{twoTreeEdgeSource}\left(d, j\right), \operatorname{twoTreeEdgeTarget}\left(d, j\right)\right)\right)) = \sum_{i : \operatorname{TwoTreeTriangles}\left(d\right)} (\operatorname{smul}\left(\operatorname{twoTreeCirculationCoordinates}\left(R, d, z, i\right), \operatorname{tau}\left(i\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.twoTree_triangle_gain_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Give the first child zero gain and give the second child the parent gain plus the prescribed triangle value. Evaluating on a circulation cancels the parent contribution introduced when the newest triangle is removed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.twoTree_filling_norm_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.twoTree_triangle_chain_coordinate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.twoTree_triangle_gain_pairing`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily.twoTree_triangles_classify`
