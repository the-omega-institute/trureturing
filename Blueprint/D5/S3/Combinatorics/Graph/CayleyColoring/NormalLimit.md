# The colored Cayley-tree central limit theorem

## Abstract

The sequential recoloring count on a uniformly rooted colored Cayley tree converges after exact standardization.

**Theorem 1.1 (Central limit theorem for the sequential move count).**

$$\forall (k: \mathbb{N}), 2 \leq k \implies \forall (K: \mathbb{N} \to Type), \forall (e: (N: \mathbb{N}) \to \operatorname{Embedding}\left(\operatorname{ZMod}\left(k\right), K\left(N\right)\right)), \operatorname{Nonempty}\left((N: \mathbb{N}) \to (s: \operatorname{Colored}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{ZMod}\left(k\right)\right)) \to \operatorname{FreePolicy}\left(K\left(N\right), \operatorname{graph}\left(s\right)\right)\right) \implies \operatorname{Eventually}\left((N: \mathbb{N} \mapsto 0<\operatorname{Var}\left((t: \operatorname{SourceSample}\left(N + 1, k\right) \mapsto \operatorname{realCast}\left(\operatorname{sourceCount}\left(e\left(N\right), t\right)\right)), \operatorname{sourceMeasure}\left(N + 1, k\right)\right)), atTop\right) \land \operatorname{Tendsto}\left((N: \mathbb{N} \mapsto \operatorname{sourceStandardizedLaw}\left(N + 1, k, e\left(N\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{gaussianReal}\left(0, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt` (`✓ std3`). ∎

*Resolves.* `Problems/de-panafieu-et-al-2026-colored-cayley-tree-clt` (proved) by `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"de-panafieu-et-al-2026-colored-cayley-tree-clt","declaration_gid":"D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

Section 6 of de Panafieu, Mathieu, Potop-Butucaru and Tixeuil asks for this limit. The palette of initial colors is fixed at size k, and each row N has N plus one vertices. The ambient palette and valid policy may depend on the row. The count records actual updates from sequential uniform enabled choices. The expectation and variance are those under the independent uniform native source inputs and the conditional scheduler law. Exact equality of count distributions transports both moments and the standardized law to the occupancy model.

**Definition 1.2 (Source count standardized by its own moments).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), [\operatorname{NeZero}\left(k\right)] \forall (K: Type), \forall (e: \operatorname{Embedding}\left(\operatorname{ZMod}\left(k\right), K\right)), \forall (s: \operatorname{SourceSample}\left(n, k\right)), \operatorname{sourceStandardized}\left(e, s\right) = \frac{(t: \operatorname{SourceSample}\left(n, k\right) \mapsto \operatorname{realCast}\left(\operatorname{sourceCount}\left(e, t\right)\right))\left(s\right) - \int (t: \operatorname{SourceSample}\left(n, k\right) \mapsto \operatorname{realCast}\left(\operatorname{sourceCount}\left(e, t\right)\right))\left(x\right) d\operatorname{sourceMeasure}\left(n, k\right)(x)}{\sqrt{\operatorname{Var}\left((t: \operatorname{SourceSample}\left(n, k\right) \mapsto \operatorname{realCast}\left(\operatorname{sourceCount}\left(e, t\right)\right)), \operatorname{sourceMeasure}\left(n, k\right)\right)}}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.sourceStandardized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here T is the source count as a real-valued function. Its mean and variance use the uniform source measure on the entire sample.

**Definition 1.3 (Law of the standardized source count).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \forall (hn: 0<n), \forall (hk: 2 \leq k), [\operatorname{NeZero}\left(k\right)] \forall (K: Type), \forall (e: \operatorname{Embedding}\left(\operatorname{ZMod}\left(k\right), K\right)), \operatorname{val}\left(\operatorname{sourceStandardizedLaw}\left(\mathit{hn}, \mathit{hk}, e\right)\right) = \operatorname{map}\left(\operatorname{sourceStandardized}\left(e\right), \operatorname{sourceMeasure}\left(n, k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.sourceStandardizedLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the pushforward of the source measure by the exactly standardized count, regarded as a probability measure on the real line.

**Theorem 1.4 (Source moments).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), 0<n \implies 2 \leq k \implies [\operatorname{NeZero}\left(k\right)] \forall (K: Type), \forall (e: \operatorname{Embedding}\left(\operatorname{ZMod}\left(k\right), K\right)), \operatorname{Nonempty}\left((s: \operatorname{Colored}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(k\right)\right)) \to \operatorname{FreePolicy}\left(K, \operatorname{graph}\left(s\right)\right)\right) \implies \int (t: \operatorname{SourceSample}\left(n, k\right) \mapsto \operatorname{realCast}\left(\operatorname{sourceCount}\left(e, t\right)\right))\left(x\right) d\operatorname{sourceMeasure}\left(n, k\right)(x) = \int \operatorname{literalCount}\left(n, n - 1\right)\left(x\right) d\operatorname{literalMeasure}\left(n, k, n - 1\right)(x) \land \operatorname{Var}\left((t: \operatorname{SourceSample}\left(n, k\right) \mapsto \operatorname{realCast}\left(\operatorname{sourceCount}\left(e, t\right)\right)), \operatorname{sourceMeasure}\left(n, k\right)\right) = \operatorname{Var}\left(\operatorname{literalCount}\left(n, n - 1\right), \operatorname{literalMeasure}\left(n, k, n - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.source_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source mean and variance are the corresponding mean and variance for the row of n minus one throws.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.sourceStandardized`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.sourceStandardizedLaw`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.source_moments`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability](FiniteProbability.md)
