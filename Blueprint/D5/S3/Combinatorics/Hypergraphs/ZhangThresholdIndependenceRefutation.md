# Independence polynomials do not determine T2-threshold hypergraphs

## Abstract

Two five-vertex T2 hypergraphs share an independence polynomial but are not isomorphic.

**Definition 1.1 (Finite uniform hypergraphs).**

$$\forall (k: \mathbb{N}), \forall (V: \operatorname{Type}) [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \operatorname{KHypergraph}\left(k, V\right) = \{edges: \operatorname{Finset}\left(\operatorname{Finset}\left(V\right)\right), \operatorname{uniform}: \forall (e: \operatorname{Finset}\left(V\right)), (e \in edges) \Rightarrow (\operatorname{Finset}.\operatorname{card}\left(e\right) = k)\}$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.KHypergraph` (`✓ std3`).

*Citation.* Erchuan Zhang (2023). *On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph*. DOI: [10.1016/j.dam.2025.07.017](https://doi.org/10.1016/j.dam.2025.07.017). URL: <https://arxiv.org/abs/2303.01024v1>.

*Commentary.*

Zhang, arXiv:2303.01024v1, p. 2: “A hypergraph H = (V, E) is an order pair of a set of vertices V and a set of hyperedges E, where each hyperedge e ∈ E is a non-empty subset of the vertex set V. Further, if |e| = k for any e ∈ E, then H is called k-uniform hypergraph, k-hypergraph or k-families.” The finite vertex type is V; edges is a finite set of finite vertex subsets, and uniform requires each edge to have k vertices. The record schema below displays both fields. The question is refuted at k = 3, where all edges are nonempty; the encoding also permits the unused values k = 0, 1, 2.

**Definition 1.2 (Independent vertex subsets).**

$$\forall (k: \mathbb{N}), \forall (V: \operatorname{Type}) [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall (H: \operatorname{KHypergraph}\left(k, V\right)), \forall (S: \operatorname{Finset}\left(V\right)), \operatorname{IsIndependent}\left(H, S\right) \Leftrightarrow (\forall (e: \operatorname{Finset}\left(V\right)), (e \in H.\operatorname{edges}) \Rightarrow (\neg (e \subseteq S)))$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.IsIndependent` (`✓ std3`).

*Citation.* Erchuan Zhang (2023). *On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph*. DOI: [10.1016/j.dam.2025.07.017](https://doi.org/10.1016/j.dam.2025.07.017). URL: <https://arxiv.org/abs/2303.01024v1>.

*Commentary.*

Zhang, p. 3: “Motivated by this idea, a vertex subset W ⊆ V is called an independent set in a hypergraph H = (V, E) if W does not include any hyperedges, i.e., ∀e ∈ E, e ⊄ W.” The variable S denotes this vertex subset. Independence excludes containment of every edge, including for the empty subset.

**Definition 1.3 (The independence polynomial).**

$$\forall (k: \mathbb{N}), \forall (V: \operatorname{Type}) [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall (H: \operatorname{KHypergraph}\left(k, V\right)), (\operatorname{indepPoly}\left(H\right): \operatorname{Polynomial}\left(\mathbb{Z}\right)) = \sum_{S \in \operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} S \mapsto \operatorname{IsIndependent}\left(H, S\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Finset}\left(V\right)\right))\right)} \operatorname{Polynomial}.\operatorname{X}^{\operatorname{Finset}.\operatorname{card}\left(S\right)}$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.indepPoly` (`✓ std3`).

*Citation.* Erchuan Zhang (2023). *On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph*. DOI: [10.1016/j.dam.2025.07.017](https://doi.org/10.1016/j.dam.2025.07.017). URL: <https://arxiv.org/abs/2303.01024v1>.

*Commentary.*

Zhang, p. 3, Eq. (8): “Given a hypergraph H = (V, E), the independence polynomial I(H; x) of H is defined as [13]” followed by I(H; x) = Σ_{W ⊆ V is independent in H} x^{|W|}. The sum includes the empty independent set. Polynomial.X is the formal indeterminate over ℤ, and Finset.univ enumerates all finite subsets of V, each once.

**Definition 1.4 (The T2-threshold property).**

$$\forall (k: \mathbb{N}), \forall (V: \operatorname{Type}) [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall (H: \operatorname{KHypergraph}\left(k, V\right)), \operatorname{IsT2Threshold}\left(H\right) \Leftrightarrow (\exists (c: V \to \mathbb{R}), \exists (t: \mathbb{R}), \forall (X: \operatorname{Finset}\left(V\right)), (\operatorname{Finset}.\operatorname{card}\left(X\right) = k) \Rightarrow (X \in H.\operatorname{edges} \Leftrightarrow t < \sum_{a \in X} c\left(a\right)))$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.IsT2Threshold` (`✓ std3`).

*Citation.* Erchuan Zhang (2023). *On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph*. DOI: [10.1016/j.dam.2025.07.017](https://doi.org/10.1016/j.dam.2025.07.017). URL: <https://arxiv.org/abs/2303.01024v1>.

*Commentary.*

Zhang, p. 12, Definition 4.1 (T2): “There exist a labeling c′ of V and a threshold τ′ such that, for any vertex subset X ⊆ V of size k, X ∈ E if and only if Σ_{x∈X} c′(x) > τ′.” Here c and t are real-valued labels and a real threshold; only subsets with exactly k vertices are tested, and the inequality is strict.

**Definition 1.5 (Isomorphism by a vertex bijection).**

$$\forall (k: \mathbb{N}), \forall (V: \operatorname{Type}) [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall (W: \operatorname{Type}) [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)], \forall (H: \operatorname{KHypergraph}\left(k, V\right)), \forall (J: \operatorname{KHypergraph}\left(k, W\right)), \operatorname{Isomorphic}\left(H, J\right) \Leftrightarrow (\exists (s: \operatorname{Equiv}\left(V, W\right)), \forall (e: \operatorname{Finset}\left(V\right)), e \in H.\operatorname{edges} \Leftrightarrow \operatorname{Finset}.\operatorname{map}\left(s.\operatorname{toEmbedding}, e\right) \in J.\operatorname{edges})$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.Isomorphic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Erchuan Zhang (2023). *On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph*. DOI: [10.1016/j.dam.2025.07.017](https://doi.org/10.1016/j.dam.2025.07.017). URL: <https://arxiv.org/abs/2303.01024v1>.

*Commentary.*

The vertex equivalence s maps each finite edge using s.toEmbedding. The equivalence of membership requires this map to carry the entire edge set onto the other edge set, with the inverse vertex equivalence providing the reverse map.

**Definition 1.6 (The positive answer to the closing question).**

$$\operatorname{claim} \Leftrightarrow (\forall (k: \mathbb{N}) (V: \operatorname{Type}) (W: \operatorname{Type}) [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)], \forall (H: \operatorname{KHypergraph}\left(k, V\right)), \forall (J: \operatorname{KHypergraph}\left(k, W\right)), (\operatorname{IsT2Threshold}\left(H\right)) \Rightarrow ((\operatorname{IsT2Threshold}\left(J\right)) \Rightarrow ((\operatorname{indepPoly}\left(H\right) = \operatorname{indepPoly}\left(J\right)) \Rightarrow (\operatorname{Isomorphic}\left(H, J\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Erchuan Zhang (2023). *On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph*. DOI: [10.1016/j.dam.2025.07.017](https://doi.org/10.1016/j.dam.2025.07.017). URL: <https://arxiv.org/abs/2303.01024v1>.

*Commentary.*

Zhang, p. 18, Section 5: “One remaining question here is about the uniqueness of the independence polynomials of antiregular k-hypergraphs. Alternatively, a more general question is, given two T2-threshold k-hypergraphs with the same independence polynomial, are they isomorphic? These are left for future work.” The positive answer is expressed as the universal implication below over all finite vertex types V and W. A pair with k = 3 suffices to answer the question negatively within the paper's k ≥ 3 range. The narrower antiregular question is separate.

**Theorem 1.7 (A five-vertex counterexample).**

$$\neg (\forall (k: \mathbb{N}) (V: \operatorname{Type}) (W: \operatorname{Type}) [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)], \forall (H: \operatorname{KHypergraph}\left(k, V\right)), \forall (J: \operatorname{KHypergraph}\left(k, W\right)), (\operatorname{IsT2Threshold}\left(H\right)) \Rightarrow ((\operatorname{IsT2Threshold}\left(J\right)) \Rightarrow ((\operatorname{indepPoly}\left(H\right) = \operatorname{indepPoly}\left(J\right)) \Rightarrow (\operatorname{Isomorphic}\left(H, J\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Erchuan Zhang (2023). *On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph*. DOI: [10.1016/j.dam.2025.07.017](https://doi.org/10.1016/j.dam.2025.07.017). URL: <https://arxiv.org/abs/2303.01024v1>.

*Commentary.*

On Fin 5, take all triples except {0,1,2}, {0,1,3}, {0,1,4} for the first hypergraph, and all triples except {0,1,2}, {0,1,3}, {0,2,3} for the second. The first labels are (0,0,1,1,1) with threshold 1; the second labels are (0,1,1,1,3) with threshold 2. Each hypergraph has exactly the empty independent set, the five singletons, the ten pairs, and its three missing triples. Hence their independence polynomials coincide. Vertex 2 of the first has degree 5; no vertex of the second has degree 5. A vertex bijection preserving edges preserves these incidence counts, so an isomorphism is impossible. This answers the general T2 question at five vertices. The arbitrary-size family, the antiregular identification and the T1 question are not established here. The source's formulas and threshold theorems do not require a positive answer to this closing question.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.IsIndependent`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.IsT2Threshold`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.Isomorphic`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.KHypergraph`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.indepPoly`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.result`
