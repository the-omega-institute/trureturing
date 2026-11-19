# Main eigenvalues and bipartite double covers

## Abstract

Finite simple graphs with isomorphic bipartite double covers have the same main eigenvalues.

**Definition 1.1 (Main adjacency eigenvalues).**

$$\forall (V : \operatorname{Type} u), \forall [\operatorname{Fintype}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall [\operatorname{DecidableRel}\left((\operatorname{Adj}\left(G\right))\right)], \forall (\lambda : \mathbb{R}), \operatorname{IsMain}\left(G, \lambda\right) \iff (\exists (x : V \to \mathbb{R}), (\forall (v : V), (\operatorname{adjMatrix}\left(G, \mathbb{R}\right) *_{v} x)(v) = \lambda \cdot x(v)) \land (\sum_{v:V} x(v) \neq 0))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.IsMain` (`✓ std3`).

*Citation.* Luke Collins and Irene Sciriha (2019). *On the Walks and Bipartite Double Coverings of Graphs with the same Main Eigenspace*. DOI: [10.48550/arXiv.1906.05790](https://doi.org/10.48550/arXiv.1906.05790). URL: <https://arxiv.org/abs/1906.05790v1>.

*Commentary.*

The coordinate sum is the inner product with the all-ones vector. Its nonvanishing guarantees that the real adjacency eigenvector is nonzero. The predicate takes a finite vertex type and decidable adjacency.

**Theorem 1.2 (Isomorphic double covers preserve the main spectrum).**

$$\forall (V : \operatorname{Type} u), \forall (W : \operatorname{Type} w), \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{Fintype}\left(W\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (H : \operatorname{SimpleGraph}\left(W\right)), \forall (e : \operatorname{Iso}\left((\operatorname{bipartiteDoubleCover}\left(G\right)), (\operatorname{bipartiteDoubleCover}\left(H\right))\right)), \forall (\lambda : \mathbb{R}), (\operatorname{IsMain}\left(G, \lambda\right) \to \operatorname{IsMain}\left(H, \lambda\right)) \land (\operatorname{IsMain}\left(H, \lambda\right) \to \operatorname{IsMain}\left(G, \lambda\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.result` (`✓ std3`). ∎

*Resolves.* `Problems/collins-sciriha-main-spectrum-double-cover` (proved) by `D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"collins-sciriha-main-spectrum-double-cover","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Luke Collins and Irene Sciriha (2019). *On the Walks and Bipartite Double Coverings of Graphs with the same Main Eigenspace*. DOI: [10.48550/arXiv.1906.05790](https://doi.org/10.48550/arXiv.1906.05790). URL: <https://arxiv.org/abs/1906.05790v1>.

*Acknowledgement.* Zhidan Yan and Wei Wang (2022). *Disproof of a conjecture on the main spectrum of generalized Bethe trees*. DOI: [10.1016/j.laa.2022.01.001](https://doi.org/10.1016/j.laa.2022.01.001). URL: <https://arxiv.org/abs/2201.01101v1>.

*Commentary.*

Question 5.8 asks, “Let G and H be two graphs with CDC(G) ≃ CDC(H). Do G and H have the same main eigenvalues?” The same question is Question 16, p. 522, in the journal version. The Mathlib cover uses the disjoint sum of two copies of the vertex type. Only cross-layer pairs are adjacent, and they are adjacent exactly when the corresponding base vertices are adjacent. The vertex types have independent universes. The graphs may be empty or disconnected, and the real parameter includes zero.

Each base vertex has a two-vertex fiber in its double cover. The equitable quotient is the base graph. Duplicating an eigenvector into the two layers doubles its coordinate sum. Adding the two layers of a cover eigenvector preserves its coordinate sum. Both operations preserve the eigenvector equation at the same eigenvalue. Reindexing by a cover isomorphism preserves both adjacency multiplication and the coordinate sum. Using the isomorphism and its inverse gives the two implications.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.IsMain`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CollinsScirihaMainSpectrum.result`
