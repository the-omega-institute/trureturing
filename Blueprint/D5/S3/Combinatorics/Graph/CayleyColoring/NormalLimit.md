# The colored Cayley-tree central limit theorem

## Abstract

The sequential recoloring count on a uniformly rooted colored Cayley tree converges after exact standardization.

**Theorem 1.1 (Central limit theorem for the sequential move count).**

$$\forall (k: \mathbb{N}), 2 \leq k \implies \forall (K: \mathbb{N} \to Type), \forall (e: (N: \mathbb{N}) \to \operatorname{Embedding}\left(\operatorname{ZMod}\left(k\right), K\left(N\right)\right)), \operatorname{Nonempty}\left((N: \mathbb{N}) \to (s: \operatorname{Colored}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{ZMod}\left(k\right)\right)) \to \operatorname{FreePolicy}\left(K\left(N\right), \operatorname{graph}\left(s\right)\right)\right) \implies \operatorname{Eventually}\left((N: \mathbb{N} \mapsto 0<\operatorname{Var}\left((t: \operatorname{SourceSample}\left(N + 1, k\right) \mapsto \operatorname{realCast}\left(\operatorname{sourceCount}\left(e\left(N\right), t\right)\right)), \operatorname{sourceMeasure}\left(N + 1, k\right)\right)), atTop\right) \land \operatorname{Tendsto}\left((N: \mathbb{N} \mapsto \operatorname{sourceStandardizedLaw}\left(N + 1, k, e\left(N\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{gaussianReal}\left(0, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

Section 6 of de Panafieu, Mathieu, Potop-Butucaru and Tixeuil asks for this limit. The palette of initial colors is fixed at size k, and each row N has N plus one vertices. The ambient palette and valid policy may depend on the row. The count records actual updates from sequential uniform enabled choices. The expectation and variance are those under the independent uniform native source inputs and the conditional scheduler law. Exact equality of count distributions transports both moments and the standardized law to the occupancy model.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability](FiniteProbability.md)
