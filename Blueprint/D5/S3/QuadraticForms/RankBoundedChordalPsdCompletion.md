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

## Separate classical criterion for planar cycle data

The following cycle criterion is separate from the chordal completion theorem above, not a consequence of it. A chordless cycle with n at least 4 is nonchordal; n=3 is included in the criterion as well. For every natural n at least 3, index vertices and edges by i=0,...,n-1, with next(i)=i+1 modulo n. Let a be any real edge function with -1 ≤ a(i) ≤ 1 for every i, and set θ(i)=arccos(a(i)) in [0,π]. There exist unit vectors p(i) in the real Euclidean plane with inner product ⟨p(i),p(next(i))⟩=a(i) on every cyclic edge if and only if there exist one common signing ε(i) in {-1,1} and an integer k such that the sum over all i of ε(i)θ(i) equals 2πk. Both the signing and the vectors are existential conclusions; neither an initial realization nor a chosen orientation of its vectors is assumed.

Equivalently, the partial real symmetric matrix with diagonal one and these cyclic edge entries has a positive semidefinite completion of rank at most 2: take the Gram matrix of the planar vectors, or factor a PSD matrix of rank at most 2 and pad with zero coordinates. Rank at most 2 does not require rank exactly 2. Endpoint values a(i)=1 or -1, repeated vectors, collinear families and families not spanning the plane are all included. No distinctness, strict angle bound or nondegeneracy assumption is imposed. The statement concerns the specified cycle edges and leaves all other pairwise inner products unspecified.

Identify the real plane isometrically with the complex plane by E=Complex.orthonormalBasisOneI.repr, sending a complex number to its real and imaginary coordinates. The norm-one vectors correspond exactly to complex numbers z(i) on the unit circle. For two unit complex numbers z and w, their real inner product is Re(w·conj(z))=Re(w/z), since the inverse of a unit complex number is its conjugate. Consequently the cyclic overlap conditions are precisely Re(q(i))=a(i), where q(i)=z(next(i))/z(i). This quotient is always defined because every z(i) has norm one.

For necessity, choose ε(i)=1 when Im(q(i)) is nonnegative and ε(i)=-1 otherwise. The principal argument of a nonzero complex number with nonnegative imaginary part is arccos(Re(q(i))/‖q(i)‖); with negative imaginary part it is the negative of that arccosine. Since ‖q(i)‖=1, arg(q(i))=ε(i)θ(i). This also treats the real-axis endpoints: q(i)=1 gives argument zero and q(i)=-1 gives argument π under the nonnegative-imaginary-part branch. The product of all q(i) is one, because its numerator is the product of all z(next(i)), a permutation of the denominator's factors. Exponentiating the sum of the signed angles therefore gives one. The unit-circle exponential has kernel 2π times the integers, so this sum is 2πk for some integer k. The winding constraint is a single closure equation for the same signing across the whole cycle.

For sufficiency, start with such a signing and integer and put q(i)=exp(ι ε(i)θ(i)), where ι is the imaginary unit. The period equation makes the product of all q(i) equal to one. Define z(i) as the prefix product of q(j) over j<i, with empty product z(0)=1. Each z(i) lies on the unit circle. For i<n-1, adjoining the next factor gives z(i+1)=z(i)q(i). For i=n-1, the full-product equation gives z(n-1)q(n-1)=1=z(0), proving the same identity across the cyclic wrap. Thus z(next(i))/z(i)=q(i) on every edge, including the last. Its real part is cos(ε(i)θ(i))=cos(θ(i))=a(i), using evenness of cosine and the closed-interval inverse-cosine identity. Applying E to each z(i) reconstructs the required unit real-plane vectors.

The classical source is M. E.-Nagy, M. Laurent and A. Varvitsiotis, Complexity of the positive semidefinite matrix completion problem with a rank constraint, arXiv:1203.6602v2, Definition 1.1 (unit-vector Gram representation, page 2) and Lemma 2.1 (cycle criterion, page 6), https://arxiv.org/abs/1203.6602v2. The latter cites the earlier M. Laurent and A. Varvitsiotis, The Gram dimension of a graph, arXiv:1112.5960v1, Section 3.1, Lemma 7 and its proof (page 10), https://arxiv.org/abs/1112.5960v1. That lemma's introductory sentence and proof specify a realization in the plane; its statement abbreviates this as a Gram representation. Version 2 omits this lemma, so the version-1 locator matters. These earlier papers are distinct from the 2014 chordal-completion reference. Attribution is citation-only; no source text or code is reproduced.

The derivation reuses the pinned Mathlib real-plane isometry, signed argument identities, unit-circle exponential and its period, finite-product reindexing and prefix-product identities. The relevant declarations are Complex.orthonormalBasisOneI, Complex.arg_of_im_nonneg_of_ne_zero, Complex.arg_of_im_neg, Circle.coe_inv_eq_conj, Circle.expHom, Circle.exp_arg, Circle.exp_eq_one, Circle.exp_two_pi_mul_int, Equiv.prod_comp, Finset.prod_Iio_mul_eq_prod_Iic, finRotate_apply, Complex.exp_ofReal_mul_I_re and Real.cos_arccos. This is exposition of established mathematics and an application of existing suppliers; it adds no retained Lean declaration or theorem Describe. It makes no uniqueness, dynamics, computational complexity or physical-realization claim.

## References

- Truth anchor: `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.exists_linearIsometryEquiv_of_inner_eq`
- Truth anchor: `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.exists_posSemidef_completion_rank_le`
- Truth anchor: `D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.gram_factor_rank`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](../Combinatorics/Graph/Chordal/Dirac.md)
