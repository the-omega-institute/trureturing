# Structured rank-one inertia

## Abstract

Structured downdates of real symmetric matrices have exact positive, negative and zero eigenvalue counts, including singular forms.

**Definition 1.1 (Quadratic pivot).**

$$(\forall (I : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] (\forall (A : \operatorname{Matrix}\left(I, I, \mathbb{R}\right)), (\forall (x : (I \to \mathbb{R})), \operatorname{pivot}\left(A, x\right) = \operatorname{dot}\left(x, \operatorname{mulVec}\left(A, x\right)\right))))$$

*Formalization.* `D5/S3/QuadraticForms/StructuredRankOneInertia.pivot` (`✓ std3`).

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

The pivot is the real quadratic value of the original matrix on x.

**Definition 1.2 (Structured downdate).**

$$(\forall (I : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] (\forall (A : \operatorname{Matrix}\left(I, I, \mathbb{R}\right)), (\forall (x : (I \to \mathbb{R})), \operatorname{downdate}\left(A, x\right) = A - \operatorname{inv}\left(\operatorname{pivot}\left(A, x\right)\right) \cdot \operatorname{vecMulVec}\left(\operatorname{mulVec}\left(A, x\right), \operatorname{mulVec}\left(A, x\right)\right))))$$

*Formalization.* `D5/S3/QuadraticForms/StructuredRankOneInertia.downdate` (`✓ std3`).

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

The coefficient is exactly the inverse pivot; the original matrix is never inverted.

**Definition 1.3 (Zero eigenvalue multiplicity).**

$$(\forall (I : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] (\forall (A : \operatorname{Matrix}\left(I, I, \mathbb{R}\right)), (\forall (h : \operatorname{IsHermitian}\left(A\right)), \operatorname{zeroIndex}\left(h\right) = \operatorname{card}\left(\{(i : I) \mid \operatorname{eigenvalues}\left(h, i\right) = 0\}\right))))$$

*Formalization.* `D5/S3/QuadraticForms/StructuredRankOneInertia.zeroIndex` (`✓ std3`).

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

Zero eigenvalues are counted with multiplicity in the finite Hermitian spectrum.

**Theorem 1.4 (Real diagonal sign counts).**

$$(\forall (I : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] (\forall (d : (I \to \mathbb{R})), ((\operatorname{posIndex}\left(\operatorname{isHermitianDiagonal}\left(d\right)\right) = \operatorname{card}\left(\{(i : I) \mid 0 < \operatorname{d}\left(i\right)\}\right)) \land (\operatorname{negIndex}\left(\operatorname{isHermitianDiagonal}\left(d\right)\right) = \operatorname{card}\left(\{(i : I) \mid \operatorname{d}\left(i\right) < 0\}\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneInertia.diagonal_counts` (`✓ std3`). ∎

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

Characteristic-polynomial roots identify the real diagonal signs with the exact spectral counts.

**Theorem 1.5 (Exact direct-sum kernel).**

$$(\forall (I : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] (\forall (A : \operatorname{Matrix}\left(I, I, \mathbb{R}\right)), (\forall (x : (I \to \mathbb{R})), (((\operatorname{IsHermitian}\left(A\right)) \land (\operatorname{pivot}\left(A, x\right) \neq 0))) \Rightarrow (((\operatorname{ker}\left(\operatorname{mulVecLin}\left(\operatorname{downdate}\left(A, x\right)\right)\right) = \operatorname{sup}\left(\operatorname{ker}\left(\operatorname{mulVecLin}\left(A\right)\right), \operatorname{span}\left(\mathbb{R}, \{ x\}\right)\right)) \land (\operatorname{Disjoint}\left(\operatorname{ker}\left(\operatorname{mulVecLin}\left(A\right)\right), \operatorname{span}\left(\mathbb{R}, \{ x\}\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneInertia.kernel_split` (`✓ std3`). ∎

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

The equality and disjointness together identify the exact direct sum of old and new null directions.

**Theorem 1.6 (Every old null direction and exactly one new direction).**

$$(\forall (I : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] (\forall (A : \operatorname{Matrix}\left(I, I, \mathbb{R}\right)), (\forall (x : (I \to \mathbb{R})), (((\operatorname{IsHermitian}\left(A\right)) \land (\operatorname{pivot}\left(A, x\right) \neq 0))) \Rightarrow (\operatorname{finrank}\left(\mathbb{R}, \operatorname{ker}\left(\operatorname{mulVecLin}\left(\operatorname{downdate}\left(A, x\right)\right)\right)\right) = \operatorname{finrank}\left(\mathbb{R}, \operatorname{ker}\left(\operatorname{mulVecLin}\left(A\right)\right)\right) + 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneInertia.nullity_downdate` (`✓ std3`). ∎

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

The direct sum adds the one-dimensional line spanned by x to the original kernel.

**Theorem 1.7 (Both complete inertia triples).**

$$(\forall (I : \operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] (\forall (A : \operatorname{Matrix}\left(I, I, \mathbb{R}\right)), (\forall (h : \operatorname{IsHermitian}\left(A\right)), (\forall (x : (I \to \mathbb{R})), (\operatorname{pivot}\left(A, x\right) \neq 0) \Rightarrow ((\exists (k : \operatorname{IsHermitian}\left(\operatorname{downdate}\left(A, x\right)\right)), (((0 < \operatorname{pivot}\left(A, x\right)) \Rightarrow (((\operatorname{posIndex}\left(h\right) = \operatorname{posIndex}\left(k\right) + 1) \land (((\operatorname{negIndex}\left(k\right) = \operatorname{negIndex}\left(h\right)) \land (\operatorname{zeroIndex}\left(k\right) = \operatorname{zeroIndex}\left(h\right) + 1)))))) \land ((\operatorname{pivot}\left(A, x\right) < 0) \Rightarrow (((\operatorname{posIndex}\left(k\right) = \operatorname{posIndex}\left(h\right)) \land (((\operatorname{negIndex}\left(h\right) = \operatorname{negIndex}\left(k\right) + 1) \land (\operatorname{zeroIndex}\left(k\right) = \operatorname{zeroIndex}\left(h\right) + 1)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneInertia.inertia_downdate` (`✓ std3`). ∎

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

The additive counts include both signs and retain all singular directions.

The index type is any finite type in Type, with a decidable equality; in particular Fin n is allowed for every natural n. A is any real Hermitian matrix, equivalently a real symmetric matrix. Delta=pivot(A,x), w=A x and M=downdate(A,x). The positive and negative indices are RHLinalg's eigenvalue counts with multiplicity. zeroIndex counts exactly the zero eigenvalues with multiplicity. The formulas retain additive identities, so the count decremented in the usual natural-subtraction presentation is proved to be at least one.

The kernel proof writes each v in ker M as v-tx plus tx, where t=Delta-inverse times the dot product of w and v. The first summand lies in ker A. Symmetry makes ker A orthogonal to w, and nonzero Delta makes its intersection with span(x) zero. Rank-nullity and the spectral rank identity identify the kernel dimension with zeroIndex. Thus no null direction of a singular A is lost.

For the other two counts, augment A by one zero coordinate. The upper triangular matrix with upper-right column x transforms diag(A,0) into [[A,w],[w-transpose,Delta]]. A lower triangular matrix with lower-left row -w-transpose/Delta transforms that same form into diag(M,Delta). Both transformers have determinant one. The existing invertible Hermitian inertia theorem applies over the reals. Characteristic-polynomial roots prove block additivity, preserving multiplicities; the real diagonal-count proof uses the real spectral theorem directly, without a complex-to-real identification.

For MO513954 revision 2, substitute A=Matrix.diagonal d. The theorem includes dimension zero vacuously and every positive finite dimension, both pivot signs and singular diagonal matrices. The source author already proposed the hyperplane/direct-sum and block-congruence mechanism. These are standard Sylvester inertia arguments, with no ordinary novelty or priority claim. The continuous-family corollary is a separate source obligation; the matrix theorem by itself does not settle the full named question. Audit registration remains unfinished under issue #25408.

## References

- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneInertia.diagonal_counts`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneInertia.downdate`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneInertia.inertia_downdate`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneInertia.kernel_split`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneInertia.nullity_downdate`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneInertia.pivot`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneInertia.zeroIndex`
- Dependency: [D5/S3/SpectralTopology/PointGapExactInertia](../SpectralTopology/PointGapExactInertia.md)
- Dependency: [D5/S3/Weil/Pick/InvertibleHermitianInertiaPullback](../Weil/Pick/InvertibleHermitianInertiaPullback.md)
