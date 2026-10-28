# Primitive signed levels on the whole legal prefix class

## Abstract

Every actual fixed-polar rank-one prefix kernel has primitive signed integer levels, including zero components.

A history is specified by three arbitrary finite chronological words w0,w1,w2 in the native letters M=[[0,1],[1,1]] and J=[[0,1],[1,0]]. The head of each word acts first. Its four recorded matrices are A0=I, A1=T(w0), A2=T(w1)A1 and A3=T(w2)A2. Empty words are permitted. Atoms inside a word are unread and do not change the reading index. These four indices are exactly 0,1,2,3; no word-length clock is substituted.

For a full real matrix X, the prefix quotient has components tr(Ai X)-tr(X), for i=1,2,3. With X=[[p,q],[r,s]], the coefficient row is (Ai00-1,Ai10,Ai01,Ai11-1): the offdiagonal entries are transposed by the trace pairing. Its rank is the dimension of the range of prefixMap on the full four-dimensional matrix space.

OrientedKernel(A,N) means that N is nonzero with determinant zero, that every full real matrix in the quotient kernel is a real multiple of N, and that det(S+N)-det(S)-det(N) is strictly positive for every entrywise positive determinant-zero real S. In dimension two, the first two conditions say rank one. The generator N is auxiliary and need not be integral or primitive. Actual positive sources remain the original positive rank-one sources; there is no trace normalization.

In the displayed formula A(w,i) is endpoint(w)(i), A(w) is the entire four-endpoint family, and B(A(w)) is its full trace-difference map. OK is exactly OrientedKernel as defined above. The auxiliary notation K(a,b,c,d) is signedMatrix(a,b,c,d), f(a,b) is the column (a,-b), and r(c,d) is the column (d,c). All matrix-vector equations use real casts of the integer coordinates and levels.

**Theorem 1.1 (Whole-class representation and converse).**

$$\forall w\in (\{0,1\}^{*})^{\{0,1,2\}}, \forall N\in \mathbb{R}^{2\times2}, \operatorname{OK}(\operatorname{A}(w),N)\iff \operatorname{rank}(\operatorname{B}(\operatorname{A}(w)))= 3\land \exists a,b,c,d\in \mathbb{Z}, \exists s\in \mathbb{R}, \exists m\in \mathbb{Z}^{\{0,1,2,3\}}, 0\leq a\land 0\leq b\land 0\leq c\land 0\leq d\land \operatorname{gcd}(a,b)= 1\land \operatorname{gcd}(c,d)= 1\land 0< a c+b d\land 0< s\land N= s \operatorname{K}(a,b,c,d)\land m(0)= 0\land \forall i\in \{0,1,2,3\}, \operatorname{A}(w,i) \operatorname{f}(a,b)= \operatorname{f}(a,b)+m(i) \operatorname{r}(c,d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/PrimitivePrefix.whole_word_primitive_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every three-word history and every real input generator N, the oriented-kernel condition is equivalent to rank three and the existence of nonnegative integers a,b,c,d, a positive real scale s, and integer levels m0,m1,m2,m3. Each pair (a,b) and (c,d) has gcd one; t=ac+bd is positive; N is s times the signed outer product (a,-b) transposed times (c,-d); m0=0; and every Ai sends (a,-b) transposed to that column plus mi times (d,c) transposed. Zero components in either primitive pair are included. The scale s is necessary for an arbitrary input generator.

The positive polar on the rank-one test sources [[uv,u],[v,1]], with u,v positive, forces the diagonal entries of N to be nonnegative and its offdiagonal entries to be nonpositive. If the trace vanished, determinant zero and nonzeroness would leave a single offdiagonal direction. The actual legal endpoints would then be triangular integral unimodular matrices with both diagonal entries one. Their quotient would also annihilate a diagonal matrix, contradicting the prescribed one-dimensional kernel.

The trace row together with the three prefix coefficient rows is therefore nonsingular. Its integer cofactors produce a nonzero integer matrix on the same real kernel line. Its orientation is chosen by the sign of the scalar relating it to N. This constructs the arithmetic generator from the original domain rather than assuming rationality, integrality or primitivity.

A nonzero nonnegative column, chosen from the first column or the negative of the second, is divided by its gcd. Integer saturation gives the other column's integer multiplier. A second gcd extraction makes the row primitive. The saturation supplier is CofactorKernel.primitive_kernel_span, with its determinant, kernel, nonzero-sum and gcd hypotheses discharged. The same supplier, applied to (d,c), gives an integer level at every endpoint. Neither argument divides by a potentially zero primitive component.

Conversely, the level equations put the signed outer product in the original quotient kernel. Its positive trace makes it nonzero; its determinant vanishes. Rank three makes this the whole kernel line. On a positive source its polar is bd p+bc q+ad r+ac s, which is strictly positive since the coefficients are nonnegative and ac+bd is positive. The prescribed native words supply actual cumulative legality throughout the converse.

If a history is presented instead by its nonnegative integral unimodular endpoints, each adjacent pair A,B has an actual forward continuation exactly when BA inverse is entrywise nonnegative. Necessity follows by cancellation of the legal multiplier. For sufficiency, the inverse of an integral determinant-plus-or-minus-one matrix is integral with the same determinant sign; the legal-monoid characterization supplies a finite forward word for BA inverse. With A0=I, imposing this at the three adjacent pairs supplies the three words used in the theorem. The inverse identifies the multiplier algebraically; it is not an acquired action. Separate endpoint legality alone does not supply those transitions.

The proof reuses LegalMatrixMonoid.legal_matrix_monoid for the exact arithmetic of native words and the pinned matrix, dimension and integer gcd APIs. It proves a representation theorem for legal prefix kernels. It does not assert global recovery, collision multiplicity, the interior normal form, or the retraction theorem.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/PrimitivePrefix.whole_word_primitive_representation`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](../../Arith/Lattices/CofactorKernel.md)
- Dependency: [D5/S3/Observer/CubicGain/LegalMatrixMonoid](LegalMatrixMonoid.md)
