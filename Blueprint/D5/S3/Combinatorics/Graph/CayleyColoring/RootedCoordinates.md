# Rooted tree color coordinates

## Abstract

A zero color-difference mark identifies a conflict at the edge to the parent.

**Theorem 1.1 (Zero marks and equal colors).**

$$\forall (V: Type), \forall (A: Type), [\operatorname{AddGroup}\left(A\right)] \forall (T: \operatorname{Tree}\left(V\right)), \forall (r: V), \forall (c: V \to A), \forall (x: \operatorname{Away}\left(V, r\right)), \operatorname{snd}\left(\operatorname{edgeColorEquiv}\left(T, r\right)\left(c\right)\right)\left(\operatorname{edgeEquiv}\left(T, r, x\right)\right) = 0 \iff c\left(\operatorname{val}\left(x\right)\right) = c\left(\operatorname{parent}\left(T, r, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.zero_pattern_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

Each non-root vertex indexes its edge to its parent. The color equivalence stores the root color and the differences on these edges. Evaluation at the indexed edge gives zero exactly when the endpoints started with the same color. This is the edge-coordinate version of the independent conflicts used in Theorem 10.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.zero_pattern_iff`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition](TreeDecomposition.md)
