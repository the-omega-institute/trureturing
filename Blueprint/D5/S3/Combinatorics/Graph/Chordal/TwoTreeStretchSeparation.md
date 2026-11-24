# Spanning-tree stretch and gain reconstruction on recursive two-trees

## Abstract

Recursive two-trees have unbounded optimal spanning-tree stretch and bounded gain errors.

Start with an oriented triangle. At each round attach a new vertex to both endpoints of each edge born in the preceding round. The two child edges follow the direction of the path through the new vertex, and the parent edge remains.

**Theorem 1.1 (Edge count).**

$$\forall d \in \operatorname{Nat}\left(\right),\; \operatorname{card}\left(\operatorname{edgeSet}\left(\operatorname{twoTree}\left(d\right)\right)\right) = 3 \cdot (\operatorname{pow}\left(2, d + 1\right) - 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_edge_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each fresh vertex introduces two edges, and the earlier edges persist.

**Theorem 1.2 (Chordality and connectivity).**

$$\forall d \in \operatorname{Nat}\left(\right),\; (\operatorname{IsChordal}\left(\operatorname{twoTree}\left(d\right)\right)) \land ((\operatorname{Connected}\left(\operatorname{twoTree}\left(d\right)\right)) \land (\operatorname{card}\left(\operatorname{TwoTreeV}\left(d\right)\right) = 3 \cdot \operatorname{pow}\left(2, d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_isChordal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each fresh vertex has two adjacent neighbors. A cycle of length at least four that visits it has a chord between those neighbors. The old graph is induced and every new vertex joins it.

**Theorem 1.3 (Exact spanning-tree stretch).**

$$\forall d \in \operatorname{Nat}\left(\right),\; (\forall T \in \operatorname{SimpleGraph}\left(\operatorname{TwoTreeV}\left(d\right)\right),\; (T \le \operatorname{twoTree}\left(d\right)) \Rightarrow ((\operatorname{IsTree}\left(T\right)) \Rightarrow (\exists u \in \operatorname{TwoTreeV}\left(d\right),\; \exists v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \land (d + 2 \le \operatorname{edist}\left(T, u, v\right))))) \land (\exists T \in \operatorname{SimpleGraph}\left(\operatorname{TwoTreeV}\left(d\right)\right),\; (T \le \operatorname{twoTree}\left(d\right)) \land ((\operatorname{IsTree}\left(T\right)) \land (\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow (\operatorname{edist}\left(T, u, v\right) \le d + 2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_min_spanning_tree_stretch_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppress the newest vertices in a spanning tree by contracting one incident edge at each new vertex. The resulting tree on the preceding round has a frontier edge whose distance is at least the previous lower bound. The fresh vertex on that edge has only one tree neighbor, so one child edge has distance at least one larger. For the upper bound, attach each new vertex as a leaf to the source of its parent edge.

**Theorem 1.4 (Reconstruction with coefficient one).**

$$\forall ell \in \operatorname{Universe}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; \forall H \in \operatorname{Type}\left(ell\right),\; [\operatorname{Group}\left(H\right)] [\operatorname{PseudoMetricSpace}\left(H\right)] [\operatorname{IsIsometricSMul}\left(H, H\right)] [\operatorname{IsIsometricSMul}\left(\operatorname{MulOpposite}\left(H\right), H\right)] , \forall g \in \operatorname{TwoTreeV}\left(d\right) \to \left(\operatorname{TwoTreeV}\left(d\right) \to H\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; (0 \le epsilon) \Rightarrow ((\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow (\operatorname{g}\left(v, u\right) = \operatorname{inv}\left(\operatorname{g}\left(u, v\right)\right))) \Rightarrow ((\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; \forall w \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), v, w\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, w\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(u, v\right) \cdot \operatorname{g}\left(v, w\right), \operatorname{g}\left(u, w\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in \operatorname{TwoTreeV}\left(d\right) \to H,\; \forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow (\operatorname{dist}\left(\operatorname{g}\left(u, v\right), \operatorname{inv}\left(\operatorname{phi}\left(u\right)\right) \cdot \operatorname{phi}\left(v\right)\right) \le epsilon))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_exists_one_approximate_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fit two core edges exactly. At a fresh vertex, transport a potential along the parent edge and then along its second child edge. The two new errors are controlled by the triangle defect and the previous error on the parent edge.

**Theorem 1.5 (An integral obstruction).**

$$\forall d \in \operatorname{Nat}\left(\right),\; \exists g \in \operatorname{TwoTreeV}\left(d\right) \to \left(\operatorname{TwoTreeV}\left(d\right) \to \operatorname{Int}\left(\right)\right),\; (\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow (\operatorname{g}\left(v, u\right) = \operatorname{neg}\left(\operatorname{g}\left(u, v\right)\right))) \land ((\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; \forall w \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), v, w\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, w\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(u, v\right) + \operatorname{g}\left(v, w\right) - \operatorname{g}\left(u, w\right)\right) \le 1)))) \land (\forall phi \in \operatorname{TwoTreeV}\left(d\right) \to \operatorname{Int}\left(\right),\; \exists u \in \operatorname{TwoTreeV}\left(d\right),\; \exists v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \land (1 \le \operatorname{norm}\left(\operatorname{g}\left(u, v\right) - \left(\operatorname{phi}\left(v\right) - \operatorname{phi}\left(u\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_integer_lower_bound_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assign unit oriented sum to each triangle. If every integral residual had absolute value less than one, the sum of the frontier residuals would vanish, contradicting the positive sum of the triangle defects.

**Definition 1.6 (Reconstruction radius).**

$$\forall d \in \operatorname{Nat}\left(\right),\; \operatorname{twoTreeBanachConstant}\left(d\right) = 1 - \frac{2}{3 \cdot 2^{d}}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTreeBanachConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value at depth zero is one third. A new round takes the average of the previous value and one.

**Theorem 1.7 (Exact real Banach constant).**

$$\forall ell \in \operatorname{Universe}\left(\right),\; \forall d \in \operatorname{Nat}\left(\right),\; (\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow (\operatorname{twoTreeCanonicalGain}\left(d, v, u\right) = \operatorname{neg}\left(\operatorname{twoTreeCanonicalGain}\left(d, u, v\right)\right))) \land ((\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; \forall w \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), v, w\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, w\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{twoTreeCanonicalGain}\left(d, u, v\right) + \operatorname{twoTreeCanonicalGain}\left(d, v, w\right) - \operatorname{twoTreeCanonicalGain}\left(d, u, w\right)\right) \le 1)))) \land ((\forall phi \in \operatorname{TwoTreeV}\left(d\right) \to \operatorname{TwoTreeCycles}\left(d\right),\; \exists u \in \operatorname{TwoTreeV}\left(d\right),\; \exists v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \land (\operatorname{twoTreeBanachConstant}\left(d\right) \le \operatorname{norm}\left(\operatorname{twoTreeCanonicalGain}\left(d, u, v\right) - \left(\operatorname{phi}\left(v\right) - \operatorname{phi}\left(u\right)\right)\right))) \land ((\forall E \in \operatorname{Type}\left(ell\right),\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), E\right)] , \forall g \in \operatorname{TwoTreeV}\left(d\right) \to \left(\operatorname{TwoTreeV}\left(d\right) \to E\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; (0 \le epsilon) \Rightarrow ((\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow (\operatorname{g}\left(v, u\right) = \operatorname{neg}\left(\operatorname{g}\left(u, v\right)\right))) \Rightarrow ((\forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; \forall w \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), v, w\right)) \Rightarrow ((\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, w\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(u, v\right) + \operatorname{g}\left(v, w\right) - \operatorname{g}\left(u, w\right)\right) \le epsilon)))) \Rightarrow (\exists phi \in \operatorname{TwoTreeV}\left(d\right) \to E,\; \forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{g}\left(u, v\right) - \left(\operatorname{phi}\left(v\right) - \operatorname{phi}\left(u\right)\right)\right) \le \operatorname{twoTreeBanachConstant}\left(d\right) \cdot epsilon))))) \land ((\forall z \in \operatorname{TwoTreeCirculation}\left(\operatorname{Real}\left(\right), d\right),\; \sum_{j : \operatorname{TwoTreeEdges}\left(d\right)} (\operatorname{smul}\left(\operatorname{val}\left(z, j\right), \operatorname{twoTreeCanonicalCirculationGain}\left(d, \operatorname{twoTreeEdgeSource}\left(d, j\right), \operatorname{twoTreeEdgeTarget}\left(d, j\right)\right)\right)) = z) \land ((\forall phi \in \operatorname{TwoTreeV}\left(d\right) \to \operatorname{TwoTreeCirculation}\left(\operatorname{Real}\left(\right), d\right),\; \exists u \in \operatorname{TwoTreeV}\left(d\right),\; \exists v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \land (\operatorname{twoTreeBanachConstant}\left(d\right) \le \operatorname{twoTreeFillingNorm}\left(d, \operatorname{twoTreeCanonicalCirculationGain}\left(d, u, v\right) - \left(\operatorname{phi}\left(v\right) - \operatorname{phi}\left(u\right)\right)\right))) \land ((\exists phi \in \operatorname{TwoTreeV}\left(d\right) \to \operatorname{TwoTreeCirculation}\left(\operatorname{Real}\left(\right), d\right),\; \forall u \in \operatorname{TwoTreeV}\left(d\right),\; \forall v \in \operatorname{TwoTreeV}\left(d\right),\; (\operatorname{Adj}\left(\operatorname{twoTree}\left(d\right), u, v\right)) \Rightarrow (\operatorname{twoTreeFillingNorm}\left(d, \operatorname{twoTreeCanonicalCirculationGain}\left(d, u, v\right) - \left(\operatorname{phi}\left(v\right) - \operatorname{phi}\left(u\right)\right)\right) \le \operatorname{twoTreeBanachConstant}\left(d\right))) \land (\forall i \in \operatorname{TwoTreeTriangles}\left(d\right),\; \operatorname{twoTreeTriangleSum}\left(d, \operatorname{twoTreeCanonicalGain}\left(d\right), i\right) = \operatorname{single}\left(1, i, 1\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_banach_exact_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the frontier residuals equals the sum of the oriented triangle coordinates. In the sum norm this gives a lower bound on a single frontier edge. The upper bound divides the core defect into thirds and assigns each fresh potential the midpoint of its two proposed values. The signed circulation coordinates identify this sum norm with the graph filling norm, and evaluation of the canonical gain on any circulation returns that circulation.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTreeBanachConstant`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_banach_exact_constant`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_exists_one_approximate_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_integer_lower_bound_one`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_isChordal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.twoTree_min_spanning_tree_stretch_eq`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](Dirac.md)
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/TwoTreeFamily](TwoTreeFamily.md)
