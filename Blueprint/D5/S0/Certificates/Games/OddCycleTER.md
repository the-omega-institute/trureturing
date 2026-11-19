# Odd-cycle TERMINATE has initial Grundy value zero

## Abstract

The original graph game TERMINATE has initial Grundy value zero on every odd cycle of length at least five.

**Definition 1.1 (Vertices of the odd cycle).**

$$\forall m \in \mathbb{N},\; \operatorname{Vertex}\left(m\right) = \operatorname{Fin}\left(2 \cdot m + 1\right)$$

*Formalization.* `D5/S0/Certificates/Games/OddCycleTER.Vertex` (`✓ std3`).

*Citation.* Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon, and Nándor Sieben (2026). *Impartial geodetic removing games on graphs*. DOI: [10.48550/arXiv.2606.05483](https://doi.org/10.48550/arXiv.2606.05483). URL: <https://arxiv.org/abs/2606.05483v1>.

*Commentary.*

The vertices are the residues modulo 2m+1. The underlying graph is Mathlib's simple cycle graph.

**Definition 1.2 (Geodetic convexity).**

$$\forall n \in \mathbb{N},\; \forall K \in \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{GeoConvex}\left(n, K\right) \Leftrightarrow \left(\forall x \in \operatorname{Fin}\left(n\right),\; \forall y \in \operatorname{Fin}\left(n\right),\; \forall p \in \operatorname{Walk}\left(\operatorname{cycleGraph}\left(n\right), x, y\right),\; \left(x \in K \land \left(y \in K \land \operatorname{length}\left(p\right) = \operatorname{dist}\left(\operatorname{cycleGraph}\left(n\right), x, y\right)\right)\right) \Rightarrow \left(\forall z \in \operatorname{Fin}\left(n\right),\; z \in \operatorname{support}\left(p\right) \Rightarrow z \in K\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/OddCycleTER.GeoConvex` (`✓ std3`).

*Citation.* Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon, and Nándor Sieben (2026). *Impartial geodetic removing games on graphs*. DOI: [10.48550/arXiv.2606.05483](https://doi.org/10.48550/arXiv.2606.05483). URL: <https://arxiv.org/abs/2606.05483v1>.

*Commentary.*

A set contains the support of every shortest walk whose endpoints belong to the set. Every walk with length equal to graph distance is a path.

**Definition 1.3 (Geodetic hull of the survivors).**

$$\forall n \in \mathbb{N},\; \forall R \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall z \in \operatorname{Fin}\left(n\right),\; z \in \operatorname{geoHull}\left(n, R\right) \Leftrightarrow \left(\forall K \in \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right),\; R \subseteq K \land \operatorname{GeoConvex}\left(n, K\right) \Rightarrow z \in K\right)$$

*Formalization.* `D5/S0/Certificates/Games/OddCycleTER.geoHull` (`✓ std3`).

*Citation.* Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon, and Nándor Sieben (2026). *Impartial geodetic removing games on graphs*. DOI: [10.48550/arXiv.2606.05483](https://doi.org/10.48550/arXiv.2606.05483). URL: <https://arxiv.org/abs/2606.05483v1>.

*Commentary.*

Intersect all geodetically convex sets containing the survivors. Shortest paths are measured in the original cycle.

**Definition 1.4 (All legal TERMINATE moves).**

$$\forall m \in \mathbb{N},\; \forall R \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m\right)\right),\; Q \in \operatorname{moves}\left(m, R\right) \Leftrightarrow \left(\operatorname{geoHull}\left(2 \cdot m + 1, R\right) = V \land \left(\exists x \in \operatorname{Vertex}\left(m\right),\; x \in R \land \operatorname{erase}\left(R, x\right) = Q\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/OddCycleTER.moves` (`✓ std3`).

*Citation.* Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon, and Nándor Sieben (2026). *Impartial geodetic removing games on graphs*. DOI: [10.48550/arXiv.2606.05483](https://doi.org/10.48550/arXiv.2606.05483). URL: <https://arxiv.org/abs/2606.05483v1>.

*Commentary.*

If the current survivor hull is the entire vertex set, deleting any one survivor is legal. The resulting hull may be proper. A proper hull at the current position gives no options.

**Definition 1.5 (Grundy recursion on survivors).**

$$\forall m \in \mathbb{N},\; \forall R \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m\right)\right),\; \operatorname{grundy}\left(m, R\right) = \operatorname{mex}\left(\{g | \exists Q \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m\right)\right),\; Q \in \operatorname{moves}\left(m, R\right) \land \operatorname{grundy}\left(m, Q\right) = g\}\right)$$

*Formalization.* `D5/S0/Certificates/Games/OddCycleTER.grundy` (`✓ std3`).

*Citation.* Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon, and Nándor Sieben (2026). *Impartial geodetic removing games on graphs*. DOI: [10.48550/arXiv.2606.05483](https://doi.org/10.48550/arXiv.2606.05483). URL: <https://arxiv.org/abs/2606.05483v1>.

*Commentary.*

Take the least natural number missing from the option values. Every option removes exactly one survivor, so survivor cardinality gives well-founded recursion.

**Definition 1.6 (Grundy value in selected-vertex coordinates).**

$$\forall m \in \mathbb{N},\; \forall S \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m\right)\right),\; \operatorname{terNim}\left(m, S\right) = \operatorname{grundy}\left(m, \operatorname{complement}\left(S\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/OddCycleTER.terNim` (`✓ std3`).

*Citation.* Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon, and Nándor Sieben (2026). *Impartial geodetic removing games on graphs*. DOI: [10.48550/arXiv.2606.05483](https://doi.org/10.48550/arXiv.2606.05483). URL: <https://arxiv.org/abs/2606.05483v1>.

*Commentary.*

Evaluate the survivor recurrence on the complement of the selected set. Deletion of an unselected vertex from the survivors adds that same vertex to the selected set.

**Theorem 1.7 (Benesh et al. Conjecture 5.5).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \operatorname{terNim}\left(m, \emptyset\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/OddCycleTER.conjecture_5_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bret J. Benesh, Dana C. Ernst, Marie Meyer, Sarah K. Salmon, and Nándor Sieben (2026). *Impartial geodetic removing games on graphs*. DOI: [10.48550/arXiv.2606.05483](https://doi.org/10.48550/arXiv.2606.05483). URL: <https://arxiv.org/abs/2606.05483v1>.

*Commentary.*

Section 5.1 defines cycle graphs for n ≥ 4, so the odd cases are exactly n = 2m+1 with m ≥ 2. Play starts with the empty selected set.

The survivor hull is full exactly when every block of m consecutive vertices contains a survivor. At the start of a two-move round with 2k+1 survivors, maintain at least k survivors in every block. For k > 2, delete the kth clockwise survivor after the first deletion's vertex in the pre-move order. The two strict arcs have k−1 and k survivors, so any block containing both deleted vertices had more than k. The reply restores the invariant with k−1.

At k = 2 the first deletion leaves four survivors and every block remains occupied. Two disjoint m-vertex blocks partition the complement of any one survivor. One block contains exactly one survivor, whose deletion ends the game. Thus each first option has a zero-valued reply by strong induction or termination. Mex then gives zero at every position satisfying the invariant, including the start.

## References

- Truth anchor: `D5/S0/Certificates/Games/OddCycleTER.GeoConvex`
- Truth anchor: `D5/S0/Certificates/Games/OddCycleTER.Vertex`
- Truth anchor: `D5/S0/Certificates/Games/OddCycleTER.conjecture_5_5`
- Truth anchor: `D5/S0/Certificates/Games/OddCycleTER.geoHull`
- Truth anchor: `D5/S0/Certificates/Games/OddCycleTER.grundy`
- Truth anchor: `D5/S0/Certificates/Games/OddCycleTER.moves`
- Truth anchor: `D5/S0/Certificates/Games/OddCycleTER.terNim`
- Dependency: [D5/S0/Certificates/Games/CrimGrundyRefutation](CrimGrundyRefutation.md)
