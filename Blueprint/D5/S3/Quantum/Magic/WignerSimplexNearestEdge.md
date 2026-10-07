# Nearest point in the four-coordinate edge polytope

## Abstract

Explicit convex mixtures give the exact L1 error to the four-coordinate edge polytope.

**Definition 1.1 (Edge vertices).**

$$\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \forall k \in \operatorname{Fin}\left(4\right),\; \operatorname{edgeVertex}\left(i, j\right)\left(k\right) = \operatorname{ite}\left((k = i) \lor (k = j), \frac{1}{2}, 0\right)$$

*Formalization.* `D5/S3/Quantum/Magic/WignerSimplexNearestEdge.edgeVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge vertex assigns one half to either endpoint and zero elsewhere.

**Definition 1.2 (Distinct endpoint vertices).**

$$\forall w \in \operatorname{Fin}\left(4\right) \to \mathbb{R},\; (w \in freeEdges) \Leftrightarrow (\exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; (i \ne j) \land (w = \operatorname{edgeVertex}\left(i, j\right)))$$

*Formalization.* `D5/S3/Quantum/Magic/WignerSimplexNearestEdge.freeEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

freeEdges consists of the vertices with two distinct endpoints.

**Theorem 1.3 (An attaining edge-polytope mixture).**

$$\forall w \in \operatorname{Fin}\left(4\right) \to \mathbb{R},\; \forall j \in \operatorname{Fin}\left(4\right),\; \forall k \in \operatorname{Fin}\left(4\right),\; (\sum_{i:\operatorname{Fin}\left(4\right)} w\left(i\right) = 1) \Rightarrow ((\forall i \in \operatorname{Fin}\left(4\right),\; w\left(j\right) \le w\left(i\right)) \Rightarrow ((\forall i \in \operatorname{Fin}\left(4\right),\; w\left(i\right) \le w\left(k\right)) \Rightarrow ((\forall i \in \operatorname{Fin}\left(4\right),\; \forall l \in \operatorname{Fin}\left(4\right),\; (i \ne l) \Rightarrow ((0 \le w\left(i\right) + w\left(l\right)) \land (w\left(i\right) + w\left(l\right) \le 1))) \Rightarrow ((\forall i \in \operatorname{Fin}\left(4\right),\; \forall l \in \operatorname{Fin}\left(4\right),\; (w\left(i\right) < 0) \Rightarrow ((w\left(l\right) < 0) \Rightarrow (i = l))) \Rightarrow ((\forall i \in \operatorname{Fin}\left(4\right),\; w\left(i\right) + w\left(j\right) \le \frac{1}{2}) \Rightarrow (\exists f \in \operatorname{Fin}\left(4\right) \to \mathbb{R},\; (f \in \operatorname{convexHull}\left(\mathbb{R}, freeEdges\right)) \land (\operatorname{norm}\left(\operatorname{toLp}\left(1, (w - f)\right)\right) = \operatorname{norm}\left(\operatorname{toLp}\left(1, w\right)\right) - 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/WignerSimplexNearestEdge.nearest_edge_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the minimum is nonnegative, five explicit nonnegative coefficients express the vector as an edge mixture. Otherwise transfer its negative minimum to a maximum coordinate. The corrected vector lies in a triangular face, and its L1 error is the original L1 norm minus one. Pair bounds, uniqueness of a negative entry and the minimum cap are explicit hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/Magic/WignerSimplexNearestEdge.edgeVertex`
- Truth anchor: `D5/S3/Quantum/Magic/WignerSimplexNearestEdge.freeEdges`
- Truth anchor: `D5/S3/Quantum/Magic/WignerSimplexNearestEdge.nearest_edge_point`
