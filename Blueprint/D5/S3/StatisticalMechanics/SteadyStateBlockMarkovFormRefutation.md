# A steady-state symmetry block without Markov form

## Abstract

An irreducible steady-state block of a four-state Markov generator is not similar to any real Markov generator, even by a complex change of basis.

Vectors are columns, Fin n indexes all n coordinates, and all finite sums include every index. Matrix.mulVec denotes matrix action on a column vector. The superscript T denotes transpose; matrix products and scalar multiples use the usual multiplication notation. The expression M.map(Complex.ofReal) embeds each real entry of M into the complex numbers. The symbol 1 denotes the identity matrix of the indicated size.

**Definition 1.1 (Real Markov generators).**

$$\forall (n: \mathbb{N}), (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((\operatorname{IsMarkovGenerator}\left(M\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), ((i \ne j) \Rightarrow (0 \le M\left(i, j\right))))) \land (\forall (j: \operatorname{Fin}\left(n\right)), (\sum_{(i: \operatorname{Fin}\left(n\right))} (M\left(i, j\right)) = 0)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.IsMarkovGenerator` (`✓ std3`).

*Citation.* Lucas Sá; Pedro Ribeiro; Tomaž Prosen; Denis Bernard (2025). *Symmetry Classes of Classical Stochastic Processes*. DOI: [10.1007/s10955-025-03423-y](https://doi.org/10.1007/s10955-025-03423-y). URL: <https://arxiv.org/abs/2406.17955v2>.

*Commentary.*

Equations (2)-(4) require real entries, nonnegative off-diagonal entries and zero column sums. The real matrix type expresses Eq. (2); the two clauses express Eqs. (3) and (4). No sign condition is imposed separately on the diagonal.

**Definition 1.2 (The steady-state block conjecture).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (N: \mathbb{N}), (\forall (L: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right)), (\forall (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right)), (\forall (p: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), ((\operatorname{IsMarkovGenerator}\left(L\right)) \Rightarrow ((U \in \operatorname{Matrix.orthogonalGroup}\left(\operatorname{Fin}\left(N\right), \mathbb{R}\right)) \Rightarrow (((U) \cdot (L) = (L) \cdot (U)) \Rightarrow (((\forall (i: \operatorname{Fin}\left(N\right)), (0 \le p\left(i\right))) \land (\sum_{(i: \operatorname{Fin}\left(N\right))} (p\left(i\right)) = 1)) \Rightarrow ((\operatorname{Matrix.mulVec}\left(L, p\right) = 0) \Rightarrow (\forall (d: \mathbb{N}), (\forall (V: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)), (\forall (u: \mathbb{R}), ((((V)^{T}) \cdot (V) = 1) \Rightarrow (((L) \cdot (V) = (V) \cdot ((((V)^{T}) \cdot (L)) \cdot (V))) \Rightarrow (((U) \cdot (V) = (u) \cdot (V)) \Rightarrow ((\forall (x: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), ((\operatorname{Matrix.mulVec}\left(U, x\right) = (u) \cdot (x)) \Rightarrow (\exists (c: (\operatorname{Fin}\left(d\right) \to \mathbb{R})), (\operatorname{Matrix.mulVec}\left(V, c\right) = x)))) \Rightarrow ((\exists (c: (\operatorname{Fin}\left(d\right) \to \mathbb{R})), (\operatorname{Matrix.mulVec}\left(V, c\right) = p)) \Rightarrow ((\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((X \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \Rightarrow (((X) \cdot (((((V)^{T}) \cdot (L)) \cdot (V)).\operatorname{map}\left(\operatorname{Complex.ofReal}\right)) = (((((V)^{T}) \cdot (L)) \cdot (V)).\operatorname{map}\left(\operatorname{Complex.ofReal}\right)) \cdot (X)) \Rightarrow (\exists (mu: \mathbb{C}), (X = (mu) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)))))))) \Rightarrow (\exists (S: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\exists (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)), ((\operatorname{IsUnit}\left(S\right)) \land ((\operatorname{IsMarkovGenerator}\left(B\right)) \land ((((S)^{-1}) \cdot (((((V)^{T}) \cdot (L)) \cdot (V)).\operatorname{map}\left(\operatorname{Complex.ofReal}\right))) \cdot (S) = (B).\operatorname{map}\left(\operatorname{Complex.ofReal}\right))))))))))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.claim` (`✓ std3`).

*Citation.* Lucas Sá; Pedro Ribeiro; Tomaž Prosen; Denis Bernard (2025). *Symmetry Classes of Classical Stochastic Processes*. DOI: [10.1007/s10955-025-03423-y](https://doi.org/10.1007/s10955-025-03423-y). URL: <https://arxiv.org/abs/2406.17955v2>.

*Commentary.*

After Eq. (5), the conjecture asks whether the irreducible block containing an invariant probability can be recast into Markov form. Here L is a real Markov generator, U is a real orthogonal matrix commuting with L, and p is stationary. The probability condition is written in full: every coordinate is nonnegative and their sum is one.

The columns of V are orthonormal and span an L-invariant subspace. They lie in the u-eigenspace of U, and the quantified condition on x says they span that whole eigenspace. The subspace contains p. Its restriction is V^T L V. Irreducibility means that every complex unitary matrix commuting with this restriction is a complex scalar multiple of the identity. Orthogonal and unitary group membership mean U^T U = U U^T = 1 and X* X = X X* = 1, respectively, where X* is conjugate transpose.

The conclusion allows any invertible complex S: IsUnit S is invertibility in the complex matrix algebra. Its conjugate of the restriction must equal a real Markov generator B embedded into the complex matrices. The dimensions N and d range over all natural numbers, with no separate positivity assumption. Appendix A proves a sufficient case under the additional assumption (A3) that the conditional probabilities are zero or one; that assumption is absent from this conjecture.

**Theorem 1.3 (A four-state counterexample).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sa-ribeiro-prosen-bernard-2024-steady-state-block-refutation` (refuted) by `D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sa-ribeiro-prosen-bernard-2024-steady-state-block-refutation","declaration_gid":"D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lucas Sá; Pedro Ribeiro; Tomaž Prosen; Denis Bernard (2025). *Symmetry Classes of Classical Stochastic Processes*. DOI: [10.1007/s10955-025-03423-y](https://doi.org/10.1007/s10955-025-03423-y). URL: <https://arxiv.org/abs/2406.17955v2>.

*Commentary.*

Take N = 4 and let L be 1/256 times the matrix with rows (-295, 25, 25, 281), (273, -303, 17, 17), (7, 263, -313, 7) and (15, 15, 271, -305). Every off-diagonal entry is positive and every column sums to zero. The stationary probability is p = (1/64)(17, 17, 15, 15). For the column vector v = (1, -1, 1, -1), set U = 1 - v v^T/2. This orthogonal involution commutes with L.

Let V be 1/2 times the four-by-three matrix with rows (1, 1, -1), (1, 1, 1), (1, -1, 1) and (1, -1, -1). Its columns are orthonormal and span the entire +1 eigenspace of U. This subspace contains p = V(1/2, 1/32, 0) and is L-invariant. Its restriction A = V^T L V has rows (0, 0, 0), (5/64, -5/4, -1) and (-1/16, 1, -5/4).

To see irreducibility, view A over the complex numbers. A unitary X commuting with A also commutes with its conjugate transpose A^T. The kernel of A^T is spanned by e_0 = (1, 0, 0), so X e_0 is a scalar multiple of e_0. The three columns e_0, A e_0 = (0, 5/64, -1/16) and A^2 e_0 = (0, -9/256, 5/32) have determinant 41/4096 and hence form a basis. Commutation with A forces X to be the same scalar on all three basis vectors.

Every real three-by-three matrix B with nonnegative off-diagonal entries satisfies 3 tr(B^2) - (tr B)^2 = (B_00 - B_11)^2 + (B_11 - B_22)^2 + (B_22 - B_00)^2 + 6(B_01 B_10 + B_02 B_20 + B_12 B_21) >= 0. For A, tr A = -5/2 and tr(A^2) = 9/8, giving 3 tr(A^2) - (tr A)^2 = -23/8. Both traces are invariant under complex similarity. Consequently no invertible complex S can make S^(-1) A S a real Markov generator.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.IsMarkovGenerator`
- Truth anchor: `D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.result`
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../TotalVariation/CycleSingleCutMinimax.md)
