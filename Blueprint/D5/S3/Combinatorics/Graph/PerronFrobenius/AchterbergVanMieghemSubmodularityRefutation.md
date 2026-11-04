# The spectral degree exponent fails submodularity

## Abstract

Five-vertex graphs refute edge-set submodularity of the spectral degree exponent.

**Definition 1.1 (The degree power mean).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (q : \mathbb{R}), \operatorname{degreePowerMean}\left(G, q\right) = (\frac{1}{(n : \mathbb{R})} \cdot (\sum_{v : \operatorname{Fin}\left(n\right)} (\operatorname{SimpleGraph.degree}\left(G, v\right) : \mathbb{R})^{q}))^{\frac{1}{q}}$$

*Formalization.* `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.degreePowerMean` (`✓ std3`).

*Citation.* Massimo A. Achterberg, Piet Van Mieghem (2025). *The spectral degree exponent of a graph*. DOI: [10.48550/arXiv.2502.01815](https://doi.org/10.48550/arXiv.2502.01815). URL: <https://arxiv.org/abs/2502.01815v1>.

*Commentary.*

“The spectral degree exponent (SDE) of a simple, undirected, non-regular (but possibly disconnected and weighted) graph G is defined as the solution for q of the equation λ₁ = ((1/N) Σ_{i=1}^N d_i^q)^{1/q}.” (Definition 2.1, equation (2.1), p. 1.) Here N is n, dᵢ is SimpleGraph.degree G v, and real exponentiation is Real.rpow. The sum ranges over all v : Fin n; division and powers take place in ℝ.

**Definition 1.2 (Regular graphs).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{IsRegular}\left(G\right)) \Leftrightarrow (\exists (r : \mathbb{N}), \operatorname{SimpleGraph.IsRegularOfDegree}\left(G, r\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.IsRegular` (`✓ std3`).

*Citation.* Massimo A. Achterberg, Piet Van Mieghem (2025). *The spectral degree exponent of a graph*. DOI: [10.48550/arXiv.2502.01815](https://doi.org/10.48550/arXiv.2502.01815). URL: <https://arxiv.org/abs/2502.01815v1>.

*Commentary.*

“The spectral degree exponent (SDE) of a simple, undirected, non-regular (but possibly disconnected and weighted) graph G is defined as the solution for q of the equation λ₁ = ((1/N) Σ_{i=1}^N d_i^q)^{1/q}.” (Definition 2.1, equation (2.1), p. 1.) Regularity means that there is a natural number r such that every vertex has degree r, expressed by SimpleGraph.IsRegularOfDegree.

**Definition 1.3 (Finite spectral degree exponents).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (q : \mathbb{R}), (\operatorname{IsSpectralDegreeExponent}\left(G, q\right)) \Leftrightarrow ((\neg \operatorname{IsRegular}\left(G\right)) \land ((2 \le q) \land (\operatorname{sSup}\left(\operatorname{spectrum}\left(\mathbb{R}, \operatorname{SimpleGraph.adjMatrix}\left(\mathbb{R}, G\right)\right)\right) = \operatorname{degreePowerMean}\left(G, q\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.IsSpectralDegreeExponent` (`✓ std3`).

*Citation.* Massimo A. Achterberg, Piet Van Mieghem (2025). *The spectral degree exponent of a graph*. DOI: [10.48550/arXiv.2502.01815](https://doi.org/10.48550/arXiv.2502.01815). URL: <https://arxiv.org/abs/2502.01815v1>.

*Commentary.*

“The spectral degree exponent (SDE) of a simple, undirected, non-regular (but possibly disconnected and weighted) graph G is defined as the solution for q of the equation λ₁ = ((1/N) Σ_{i=1}^N d_i^q)^{1/q}.” (Definition 2.1, equation (2.1), p. 1.) “The spectral degree exponent (SDE) exists, is unique and is bounded in q ∈ [2, ∞].” (Theorem 2.2, p. 2.) The displayed predicate selects finite real solutions q ≥ 2 for non-regular unweighted graphs. “The spectral radius λ₁ is the largest eigenvalue of the weighted adjacency matrix A of the graph G.” (p. 1.) Its real adjacency spectrum has supremum sSup (spectrum ℝ (G.adjMatrix ℝ)). All four graphs used below have such solutions; no statement about infinite exponents is required.

**Definition 1.4 (Submodularity on a fixed vertex set).**

$$(claim) \Leftrightarrow ((\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (H : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (qG : \mathbb{R}), \forall (qH : \mathbb{R}), \forall (qU : \mathbb{R}), \forall (qI : \mathbb{R}), (\operatorname{IsSpectralDegreeExponent}\left(G, qG\right)) \Rightarrow ((\operatorname{IsSpectralDegreeExponent}\left(H, qH\right)) \Rightarrow ((\operatorname{IsSpectralDegreeExponent}\left(\operatorname{SemilatticeSup.sup}\left(G, H\right), qU\right)) \Rightarrow ((\operatorname{IsSpectralDegreeExponent}\left(\operatorname{SemilatticeInf.inf}\left(G, H\right), qI\right)) \Rightarrow (qU + qI \le qG + qH))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.claim` (`✓ std3`).

*Citation.* Massimo A. Achterberg, Piet Van Mieghem (2025). *The spectral degree exponent of a graph*. DOI: [10.48550/arXiv.2502.01815](https://doi.org/10.48550/arXiv.2502.01815). URL: <https://arxiv.org/abs/2502.01815v1>.

*Commentary.*

“Several other properties of the SDE have not yet been established, e.g. whether the SDE is submodular or if the SDE can be used successfully in applications to enhance or reduce assortativity.” (Section 7, p. 15.) The ground set consists of possible edges on Fin n. The lattice operations are edge union and intersection. The four real exponents satisfy their respective equations before the submodular inequality is required.

**Theorem 1.5 (A five-vertex counterexample).**

$$\neg (\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (H : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (qG : \mathbb{R}), \forall (qH : \mathbb{R}), \forall (qU : \mathbb{R}), \forall (qI : \mathbb{R}), (\operatorname{IsSpectralDegreeExponent}\left(G, qG\right)) \Rightarrow ((\operatorname{IsSpectralDegreeExponent}\left(H, qH\right)) \Rightarrow ((\operatorname{IsSpectralDegreeExponent}\left(\operatorname{SemilatticeSup.sup}\left(G, H\right), qU\right)) \Rightarrow ((\operatorname{IsSpectralDegreeExponent}\left(\operatorname{SemilatticeInf.inf}\left(G, H\right), qI\right)) \Rightarrow (qU + qI \le qG + qH)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/achterberg-van-mieghem-2025-spectral-degree-exponent-submodularity` (refuted) by `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"achterberg-van-mieghem-2025-spectral-degree-exponent-submodularity","declaration_gid":"D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Massimo A. Achterberg, Piet Van Mieghem (2025). *The spectral degree exponent of a graph*. DOI: [10.48550/arXiv.2502.01815](https://doi.org/10.48550/arXiv.2502.01815). URL: <https://arxiv.org/abs/2502.01815v1>.

*Commentary.*

Take E₀ = {01, 02, 03, 14, 23}, e = 24 and f = 34 on five vertices. The exponents of E₀ and E₀ ∪ {e,f} lie strictly between 3 and 4, whereas those of E₀ ∪ {e} and E₀ ∪ {f} lie strictly between 2 and 3. Characteristic polynomials bound the largest eigenvalues, exact degree moments bound the power means, and continuity supplies these finite solutions. Thus the union and intersection exponents have sum greater than 6, while the two single-edge additions have sum less than 6. The source definitions and earlier theorems are unaffected.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.IsRegular`
- Truth anchor: `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.IsSpectralDegreeExponent`
- Truth anchor: `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.degreePowerMean`
- Truth anchor: `D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation](../TokenGraph/CutBoundRefutation.md)
- Dependency: [D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate](../../../Quantum/BlockNorm/SpikeEdgeEstimate.md)
