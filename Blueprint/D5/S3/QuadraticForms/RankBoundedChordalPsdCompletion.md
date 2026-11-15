# Rank-Bounded Positive Semidefinite Completion on Chordal Graphs

## Abstract

Clique-positive real tables on finite chordal graphs have PSD completions with the same local rank bound.

**Theorem 1.1 (Every diagonal and graph edge is preserved).**

$$\forall (V : Type), [\operatorname{Finite}\left(V\right)] \forall (d : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (A : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), (\operatorname{IsChordal}\left(G\right) \land \forall (C : \operatorname{Set}\left(V\right)), \operatorname{IsClique}\left(G, C\right) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{Restrict}\left(A, C\right)\right) \land \operatorname{rank}\left(\operatorname{Restrict}\left(A, C\right)\right) \leq d) \Rightarrow \exists (B : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), \operatorname{PosSemidef}\left(B\right) \land \operatorname{rank}\left(B\right) \leq d \land \forall (i : V), \forall (j : V), (i = j \lor \operatorname{Adj}\left(G, i, j\right)) \Rightarrow \operatorname{entry}\left(B, i, j\right) = \operatorname{entry}\left(A, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.exists_posSemidef_completion_rank_le` (`✓ std3`). ∎

*Citation.* Monique Laurent and Antonios Varvitsiotis (2014). *A new graph parameter related to bounded rank positive semidefinite matrix completions*. DOI: [10.1007/s10107-013-0648-x](https://doi.org/10.1007/s10107-013-0648-x). URL: <https://arxiv.org/abs/1204.0734>.

*Commentary.*

Let V be any finite type in any universe, d any natural number, G a chordal simple graph on V, and A any real matrix on V. For every clique C, assume the principal block Restrict(A,C) is positive semidefinite and has real matrix rank at most d. Then a real matrix B on V exists which is positive semidefinite, has real matrix rank at most d, and agrees with A on every diagonal and graph edge. Restrict denotes Matrix.submatrix with both maps the subtype inclusion. Cliques include the empty set and singletons; d may be zero.

Laurent and Varvitsiotis state the minimum-rank chordal completion result in their introduction. Their Lemma 2 proof explains the orthogonal alignment on an overlap. This is established mathematics. Unspecified nonedge input entries may be nonsymmetric, and no global completion or realization is given as a premise.

Remove a simplicial vertex v using the finite chordal Dirac theorem. Induction realizes the remaining graph in the unchanged Euclidean space with d coordinates. The clique consisting of v and its neighbours has a Gram factor in that same space because its PSD rank is at most d. The local and old neighbour vectors have equal pairwise inner products. An ambient linear isometric equivalence carries the local neighbours to the old neighbours. Apply it to the local vector for v and leave every old vector unchanged. Inner products with every neighbour, and the prescribed diagonal at v, are preserved. Taking the Gram matrix gives positivity; a factor with d rows bounds its rank by d.

The local rank factorization and equal-Gram ambient isometry are adapted from TauCetiProject/TauCeti at revision 0ae45cec5df3d83669e6a8403d229ddbf562d89c. The precise consumed sources, original authors and Apache license are identified in the cited literature note and the Lean source. The alignment includes dependent, zero and empty families. It needs no inverse of an overlap Gram matrix and adds no residual coordinate. Empty carriers, isolated vertices, disconnected graphs and singular clique blocks remain in scope.

For a conditional fixed-dimension model, put d=3 or d=6 and prescribe diagonal one. Assume the full local PSD and rank bound on every clique; a clique-size bound is not substituted for the rank premise. The resulting completion has a common real Gram realization in that fixed dimension, and every vector has norm one. Every specified edge retains its input inner product. This asserts existence, without uniqueness, dynamics or a choice of realization supplied in advance.

**Theorem 1.2 (A prescribed rank bound fixes the Gram ambient dimension).**

$$\forall (V : Type), [\operatorname{Finite}\left(V\right)] \forall (d : \mathbb{N}), \forall (A : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), (\operatorname{PosSemidef}\left(A\right) \land \operatorname{rank}\left(A\right) \leq d) \Rightarrow \exists (p : V \to \operatorname{Euclidean}\left(d\right)), \forall (i : V), \forall (j : V), \operatorname{innerReal}\left(\operatorname{value}\left(p, i\right), \operatorname{value}\left(p, j\right)\right) = \operatorname{entry}\left(A, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.gram_factor_rank` (`✓ std3`). ∎

*Citation.* Monique Laurent and Antonios Varvitsiotis (2014). *A new graph parameter related to bounded rank positive semidefinite matrix completions*. DOI: [10.1007/s10107-013-0648-x](https://doi.org/10.1007/s10107-013-0648-x). URL: <https://arxiv.org/abs/1204.0734>.

*Commentary.*

For any finite type V, any natural d and any real PSD matrix A on V of real matrix rank at most d, there is a family p in the real Euclidean space with exactly d coordinates whose pairwise inner products are precisely A. The finite type may inhabit any universe. Empty V, d=0 and singular matrices are included. Euclidean(d) denotes EuclideanSpace over the real numbers indexed by Fin d. The rank factorization is the attributed TauCeti supplier described in the cited note; this API exposes that original proof for reuse. The cycle theorem consumes it with d=3 in its converse.

**Theorem 1.3 (Equal Gram families align in the same ambient space).**

$$\forall (K : Type), \forall (E : Type), \forall (I : Type), [\operatorname{RCLike}\left(K\right), \operatorname{NormedAddCommGroup}\left(E\right), \operatorname{InnerProductSpace}\left(K, E\right), \operatorname{FiniteDimensional}\left(K, E\right)] \forall (v : I \to E), \forall (w : I \to E), (\forall (i : I), \forall (j : I), \operatorname{inner}\left(K, \operatorname{value}\left(v, i\right), \operatorname{value}\left(v, j\right)\right) = \operatorname{inner}\left(K, \operatorname{value}\left(w, i\right), \operatorname{value}\left(w, j\right)\right)) \Rightarrow \exists (e : \operatorname{IsometricAut}\left(K, E\right)), \forall (i : I), \operatorname{value}\left(e, \operatorname{value}\left(v, i\right)\right) = \operatorname{value}\left(w, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.exists_linearIsometryEquiv_of_inner_eq` (`✓ std3`). ∎

*Citation.* Monique Laurent and Antonios Varvitsiotis (2014). *A new graph parameter related to bounded rank positive semidefinite matrix completions*. DOI: [10.1007/s10107-013-0648-x](https://doi.org/10.1007/s10107-013-0648-x). URL: <https://arxiv.org/abs/1204.0734>.

*Commentary.*

Let K be any RCLike field and E any normed additive commutative group with an inner-product-space structure over K, finite-dimensional over K. Let I be any index type, in any universe, and v,w be families I to E. If all their pairwise K-inner products agree, an ambient linear isometric equivalence e from E to E exists with e(v(i))=w(i) for every i. There is no finiteness assumption on I and no independence, spanning or nonzero assumption on either family. IsometricAut(K,E) denotes E equivalent to itself by a K-linear isometry. The attributed TauCeti construction extends the equal-Gram isometry between the spans to the original ambient space. The cycle construction consumes it on its two endpoints, including repeated endpoints.

## References

- Truth anchor: `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.exists_linearIsometryEquiv_of_inner_eq`
- Truth anchor: `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.exists_posSemidef_completion_rank_le`
- Truth anchor: `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.gram_factor_rank`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](../Combinatorics/Graph/Chordal/Dirac.md)
