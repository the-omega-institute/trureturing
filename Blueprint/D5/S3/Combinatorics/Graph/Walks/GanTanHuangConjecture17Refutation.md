# A counterexample to Gan, Tan and Huang's Conjecture 1.7

## Abstract

Six clique vertices with three private leaves each meet the proposed degree threshold at d = k = 8.

**Definition 1.1 (Conjecture 1.7).**

$$claim \Leftrightarrow (\forall (V : Type), [\operatorname{Fintype}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (d : \mathbb{N}), \forall (k : \mathbb{N}), (0 < k) \Rightarrow ((k \le d) \Rightarrow ((d < \operatorname{card}\left(V\right)) \Rightarrow ((\operatorname{Connected}\left(G\right)) \Rightarrow ((\frac{(\left\lfloor\frac{(k : \mathbb{Z}) - 3}{4}\right\rfloor : \mathbb{Q}) \cdot \left((\operatorname{card}\left(V\right) : \mathbb{Q}) - 1\right)}{(d : \mathbb{Q})} + \left(1 - \frac{(\left\lfloor\frac{(k : \mathbb{Z}) - 3}{4}\right\rfloor : \mathbb{Q})}{(d : \mathbb{Q})}\right) \cdot \frac{\left((\operatorname{card}\left(V\right) : \mathbb{Q}) - 1\right) \cdot (\left\lfloor\frac{(k : \mathbb{Z}) - 3}{4}\right\rfloor : \mathbb{Q})}{(\left\lfloor\frac{(k : \mathbb{Z}) - 3}{4}\right\rfloor : \mathbb{Q}) + (d : \mathbb{Q}) \cdot \left((d : \mathbb{Q}) - 1\right)} + 2 \le (\operatorname{ncard}\left(\{v \mid d \le \operatorname{ncard}\left(\operatorname{neighborSet}\left(G, v\right)\right)\}\right) : \mathbb{Q})) \Rightarrow (\exists (p : \operatorname{Fin}\left(k + 1\right) \to V), \operatorname{Injective}\left(p\right) \land (\forall (i : \operatorname{Fin}\left(k\right)), \operatorname{Adj}\left(G, \operatorname{p}\left(\operatorname{castSucc}\left(i\right)\right), \operatorname{p}\left(\operatorname{succ}\left(i\right)\right)\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.claim` (`✓ std3`).

*Citation.* Zhiyong Gan; Zhiliang Tan; Yi Huang (2026). *An extremal question of Erdős et al. on cycles*. DOI: [10.48550/arXiv.2611.22824](https://doi.org/10.48550/arXiv.2611.22824). URL: <https://arxiv.org/abs/2611.22824v1>.

*Commentary.*

The vertex type V carries a Fintype instance. The vertex count n is its cardinality, and Mathlib's SimpleGraph encodes the finite simple undirected graph on V. The source's high-degree count is the cardinality of the set of vertices whose neighbor set has at least d elements. Fin k consists of the indices 0 through k−1, so castSucc embeds each index into Fin(k+1) with the same value and succ embeds it at the next value. The injective sequence has exactly k+1 vertices.

The floor q is evaluated by dividing k−3 in the integers by positive 4. All arithmetic in the threshold after that floor, including n−1 and d−1, is rational. The positive source domain gives d > 0 and q ≥ −1. At d = 1 we have k = 1 and q + d(d−1) = −1. For d ≥ 2 the product d(d−1) is at least 2, so q + d(d−1) ≥ 1.

**Theorem 1.2 (A clique with private leaves).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gan-tan-huang-2026-conjecture-1-7` (refuted) by `D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gan-tan-huang-2026-conjecture-1-7","declaration_gid":"D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zhiyong Gan; Zhiliang Tan; Yi Huang (2026). *An extremal question of Erdős et al. on cycles*. DOI: [10.48550/arXiv.2611.22824](https://doi.org/10.48550/arXiv.2611.22824). URL: <https://arxiv.org/abs/2611.22824v1>.

*Commentary.*

The vertices are the disjoint sum of Fin 6 and Fin 6 × Fin 3. The first summand forms a clique, and each vertex (i,j) of the second summand is adjacent only to clique vertex i. Every vertex reaches core vertex 0, through its own core vertex if it is a leaf. There are 24 vertices. The six core vertices have degree 8 and the 18 leaves have degree 1. At d = k = 8 the floor is 1, the second denominator is 57, and the threshold is 298/57, below 6 by 44/57.

In a hypothetical nine-vertex path, injectivity makes the predecessor and successor of each interior vertex distinct. A leaf has a single neighbor, so all seven interior vertices must be core vertices. Their distinct core labels would give an injection from Fin 7 into Fin 6. Mathlib's finite-cardinality bound for injections rules this out.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.result`
