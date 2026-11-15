# Real Positive Semidefinite Completion on Chordal Graphs

## Abstract

Clique-positive real tables on finite chordal graphs have positive semidefinite completions, including singular blocks.

**Theorem 1.1 (Every diagonal and graph edge is preserved).**

$$\forall (V : Type), [\operatorname{Finite}\left(V\right)] \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (A : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), (\operatorname{IsChordal}\left(G\right) \land \forall (C : \operatorname{Set}\left(V\right)), \operatorname{IsClique}\left(G, C\right) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{Restrict}\left(A, C\right)\right)) \Rightarrow \exists (B : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), \operatorname{PosSemidef}\left(B\right) \land \forall (i : V), \forall (j : V), (i = j \lor \operatorname{Adj}\left(G, i, j\right)) \Rightarrow \operatorname{entry}\left(B, i, j\right) = \operatorname{entry}\left(A, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ChordalPsdCompletion.exists_posSemidef_completion` (`✓ std3`). ∎

*Citation.* Lieven Vandenberghe; Martin S. Andersen (2015). *Chordal Graphs and Semidefinite Optimization*. DOI: [10.1561/2400000006](https://doi.org/10.1561/2400000006). URL: <https://www.seas.ucla.edu/~vandenbe/publications/chordalsdp.pdf>.

*Commentary.*

Let V be any finite type, in any universe, G a simple graph on V, and A a real matrix indexed by V. Assume G is chordal and the principal restriction of A to every clique C is positive semidefinite. There exists a real positive semidefinite matrix B on the same V with B(i,j)=A(i,j) whenever i=j or G has the edge i,j. Restrict(A,C) in the formula is Matrix.submatrix A Subtype.val Subtype.val, indexed by the subtype of vertices in C. Cliques include singletons and the empty set.

This is the positive semidefinite existence direction of Vandenberghe and Andersen's Theorem 10.1, printed page 356. It is established mathematics, not an originality or open-problem claim. The real table A need not be symmetric on unspecified nonedges. The assumptions impose the required symmetry on each specified clique; B is symmetric everywhere. There is no constraint on the unspecified nonedge entries of B.

Strong induction on the number of vertices uses SimpleGraph.IsChordal.exists_isSimplicial and IsChordal.induce from the existing Dirac module. Remove a simplicial vertex v and recursively complete the induced graph. Its positive semidefinite completion has a real Gram factor x. The clique consisting of v and its neighbours has a separate real Gram factor y. Both factors come directly from Matrix.posSemidef_iff_eq_sum_vecMulVec, which includes singular matrices.

On the neighbours, the two Gram families agree because their entries come from the same A. The original WeightedGramContraction.contraction_of_gram supplies a contraction Z carrying each local neighbour vector to its old vector. Equality of neighbour norms implies Z-adjoint x(k)=y(k), so the candidate Z(y(v)) has every required mixed inner product. Its norm can be smaller than the prescribed norm. Embed the old space as the first factor of its L2 product with the reals, and give the new vertex the extra coordinate sqrt(norm(y(v))^2-norm(Z(y(v)))^2). Contractivity makes this real; its square restores the prescribed diagonal. The Gram matrix of this combined family is the completion.

A separate conditional finite-memory model fixes natural numbers N and M and one real table A on vertices 0 through N, with diagonal one. Assume each consecutive window [a,a+M] intersected with this horizon has a positive semidefinite principal block. Retain precisely the pairs with absolute index difference at most M, including the diagonal. This band graph has the natural index order as a perfect elimination order: two later neighbours of the same vertex differ by at most M. Every nonempty clique lies in the window starting at its least index; the empty clique is harmless. The theorem therefore supplies a PSD completion, and the actual real Gram factor supplies a common finite-dimensional family p with norm(p(i))=1 and inner(p(i),p(j))=A(i,j) for every retained pair. Positivity of shorter consecutive windows follows by principal restriction. Overlap agreement comes from using one table, not separate unrelated realizations.

This is an explicitly added conditional model motivated by finite-memory windows, not a requirement already stated by existing vector presets. The band application reuses the general theorem. It asserts neither a fixed dimension such as three or six, uniqueness, dynamics, interior slack nor an infinite extension. N=0, M=0 and singular windows are included. A separate boundary check uses the specified entries d(i)d(j) for an arbitrary real family d and arbitrary chordal graph, while putting -100 on every unspecified nonedge of the input table. Clique restrictions are rank-one Gram matrices, including zero and singular cases; the output preserves only the prescribed entries.

The empty carrier uses the empty zero matrix. An isolated eliminated vertex has an empty neighbour family, and disconnected graphs require no connectedness assumption. Zero residuals and singular neighbour blocks are allowed. No inverse, positive definiteness, nonsingular separator, prescribed rank, supplied global completion or fixed ambient dimension is assumed.

## References

- Truth anchor: `D5/S3/QuadraticForms/ChordalPsdCompletion.exists_posSemidef_completion`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](../Combinatorics/Graph/Chordal/Dirac.md)
- Dependency: [D5/S3/QuadraticForms/WeightedGramContraction](WeightedGramContraction.md)
