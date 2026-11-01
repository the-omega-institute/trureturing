# Continuous structured downdates on the original domain

## Abstract

The original finite-puncture simplex domain supplies nonemptiness, constant pivot sign and one globally unique negative diagonal coordinate.

**Definition 1.1 (Independent barycentric coordinates).**

$$(\forall (m : \mathbb{N}), \operatorname{openSimplex}\left(m\right) = \operatorname{setOf}\left((u : (\operatorname{Fin}\left(m\right) \to \mathbb{R})) \mapsto (((\forall (i : \operatorname{Fin}\left(m\right)), 0 < \operatorname{u}\left(i\right))) \land (\sum_{(i : \operatorname{Fin}\left(m\right))} \operatorname{u}\left(i\right) < 1))\right))$$

*Formalization.* `D5/S3/QuadraticForms/StructuredRankOneFamily.openSimplex` (`✓ std3`).

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

The omitted barycentric coordinate is positive because the displayed sum is strictly less than one.

**Theorem 1.2 (Finite punctures preserve path connectedness).**

$$(\forall (n : \mathbb{N}), (3 \le n) \Rightarrow ((\forall (X : \operatorname{Type}\left(\right)), [\operatorname{TopologicalSpace}\left(X\right)] (\operatorname{Nonempty}\left(\operatorname{Homeomorph}\left(X, \operatorname{openSimplex}\left(n - 1\right)\right)\right)) \Rightarrow ((\forall (A : \operatorname{Set}\left(X\right)), (\operatorname{Finite}\left(A\right)) \Rightarrow (\operatorname{IsPathConnected}\left(\operatorname{compl}\left(A\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneFamily.punctured_simplex_pathConnected` (`✓ std3`). ∎

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

The explicit log-ratio chart transports the finite punctures to real space of dimension greater than one.

**Theorem 1.3 (Constant sign and the globally unique negative index).**

$$(\forall (n : \mathbb{N}), (3 \le n) \Rightarrow ((\forall (X : \operatorname{Type}\left(\right)), [\operatorname{TopologicalSpace}\left(X\right)] (\operatorname{Nonempty}\left(\operatorname{Homeomorph}\left(X, \operatorname{openSimplex}\left(n - 1\right)\right)\right)) \Rightarrow ((\forall (A : \operatorname{Set}\left(X\right)), (\operatorname{Finite}\left(A\right)) \Rightarrow ((\forall (d : (\operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{R}))), (\forall (x : (\operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{R}))), (((\operatorname{Continuous}\left(d\right)) \land (((\operatorname{Continuous}\left(x\right)) \land ((((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), \operatorname{pivot}\left(\operatorname{diagonal}\left(\operatorname{d}\left(y\right)\right), \operatorname{x}\left(y\right)\right) \neq 0)) \land ((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), \operatorname{PosSemidef}\left(\operatorname{downdate}\left(\operatorname{diagonal}\left(\operatorname{d}\left(y\right)\right), \operatorname{x}\left(y\right)\right)\right))))))))) \Rightarrow (((\operatorname{SetNonempty}\left(\operatorname{compl}\left(A\right)\right)) \land (((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), 0 < \operatorname{pivot}\left(\operatorname{diagonal}\left(\operatorname{d}\left(y\right)\right), \operatorname{x}\left(y\right)\right)) \lor (((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), \operatorname{pivot}\left(\operatorname{diagonal}\left(\operatorname{d}\left(y\right)\right), \operatorname{x}\left(y\right)\right) < 0)) \land (\operatorname{ExistsUnique}\left((j : \operatorname{Fin}\left(n\right)) \mapsto (((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), \operatorname{d}\left(y, j\right) < 0)) \land ((\forall (i : \operatorname{Fin}\left(n\right)), (i \neq j) \Rightarrow ((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), 0 \le \operatorname{d}\left(y, i\right))))))\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneFamily.continuous_family` (`✓ std3`). ∎

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

Nonemptiness, the strict sign dichotomy and uniqueness of one global coordinate are all included.

**Theorem 1.4 (The complete revision-two conjunction).**

$$(((\forall (n : \mathbb{N}), (\forall (d : (\operatorname{Fin}\left(n\right) \to \mathbb{R})), (\forall (x : (\operatorname{Fin}\left(n\right) \to \mathbb{R})), (\operatorname{pivot}\left(\operatorname{diagonal}\left(d\right), x\right) \neq 0) \Rightarrow (\exists (k : \operatorname{IsHermitian}\left(\operatorname{downdate}\left(\operatorname{diagonal}\left(d\right), x\right)\right)), (((0 < \operatorname{pivot}\left(\operatorname{diagonal}\left(d\right), x\right)) \Rightarrow (((\operatorname{posIndex}\left(\operatorname{isHermitianDiagonal}\left(d\right)\right) = \operatorname{posIndex}\left(k\right) + 1) \land (((\operatorname{negIndex}\left(k\right) = \operatorname{negIndex}\left(\operatorname{isHermitianDiagonal}\left(d\right)\right)) \land (\operatorname{zeroIndex}\left(k\right) = \operatorname{zeroIndex}\left(\operatorname{isHermitianDiagonal}\left(d\right)\right) + 1)))))) \land ((\operatorname{pivot}\left(\operatorname{diagonal}\left(d\right), x\right) < 0) \Rightarrow (((\operatorname{posIndex}\left(k\right) = \operatorname{posIndex}\left(\operatorname{isHermitianDiagonal}\left(d\right)\right)) \land (((\operatorname{negIndex}\left(\operatorname{isHermitianDiagonal}\left(d\right)\right) = \operatorname{negIndex}\left(k\right) + 1) \land (\operatorname{zeroIndex}\left(k\right) = \operatorname{zeroIndex}\left(\operatorname{isHermitianDiagonal}\left(d\right)\right) + 1)))))))))))) \land ((\forall (n : \mathbb{N}), (3 \le n) \Rightarrow ((\forall (X : \operatorname{Type}\left(\right)), [\operatorname{TopologicalSpace}\left(X\right)] (\operatorname{Nonempty}\left(\operatorname{Homeomorph}\left(X, \operatorname{openSimplex}\left(n - 1\right)\right)\right)) \Rightarrow ((\forall (A : \operatorname{Set}\left(X\right)), (\operatorname{Finite}\left(A\right)) \Rightarrow ((\forall (d : (\operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{R}))), (\forall (x : (\operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{R}))), (((\operatorname{Continuous}\left(d\right)) \land (((\operatorname{Continuous}\left(x\right)) \land ((((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), \operatorname{pivot}\left(\operatorname{diagonal}\left(\operatorname{d}\left(y\right)\right), \operatorname{x}\left(y\right)\right) \neq 0)) \land ((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), \operatorname{PosSemidef}\left(\operatorname{downdate}\left(\operatorname{diagonal}\left(\operatorname{d}\left(y\right)\right), \operatorname{x}\left(y\right)\right)\right))))))))) \Rightarrow (((\operatorname{SetNonempty}\left(\operatorname{compl}\left(A\right)\right)) \land (((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), 0 < \operatorname{pivot}\left(\operatorname{diagonal}\left(\operatorname{d}\left(y\right)\right), \operatorname{x}\left(y\right)\right)) \lor (((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), \operatorname{pivot}\left(\operatorname{diagonal}\left(\operatorname{d}\left(y\right)\right), \operatorname{x}\left(y\right)\right) < 0)) \land (\operatorname{ExistsUnique}\left((j : \operatorname{Fin}\left(n\right)) \mapsto (((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), \operatorname{d}\left(y, j\right) < 0)) \land ((\forall (i : \operatorname{Fin}\left(n\right)), (i \neq j) \Rightarrow ((\forall (y : \operatorname{Subtype}\left(\operatorname{compl}\left(A\right)\right)), 0 \le \operatorname{d}\left(y, i\right))))))\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/StructuredRankOneFamily.mo513954_revision2` (`✓ std3`). ∎

*Citation.* Lucid (MathOverflow user 596445) (2026). *Inertia of a singular diagonal matrix after a structured rank-one downdate, revision 2*. URL: <https://mathoverflow.net/revisions/513954/2>.

*Commentary.*

Both universal source clauses hold together, with the matrix clause quantified over every finite dimension.

openSimplex(m) is the set of m positive real independent barycentric coordinates whose sum is less than one. Its omitted last coordinate is one minus that sum and is strictly positive. Thus openSimplex(n-1) is exactly an open (n-1)-simplex with n barycentric coordinates. X is any topological space with the displayed homeomorphism e to this model; A is any finite subset of X, and Y is the subtype of points outside A.

The chart from real m-space sends t to exp(t_i)/(1+sum exp(t_j)). Its inverse sends u to log(u_i/(1-sum u_j)). Both maps are continuous and inverse on their full domains. The image of A under the transported chart is finite. For n at least three the real vector-space dimension n-1 is greater than one, so Mathlib's countable-complement theorem supplies a nonempty path-connected complement. Homeomorphic transport establishes nonemptiness and path connectedness of Y. Neither is added as an independent family premise.

The diagonal entries d and vector x are continuous on exactly Y. Delta(y)=pivot(diagonal(d(y)),x(y)) is continuous, nonzero at every point, and therefore has one constant strict sign on connected Y. M is exactly the structured downdate, not an independently supplied family. Its continuity follows from these data and nonvanishing Delta. The positive-semidefinite premise applies at every point of Y.

In the negative-sign case, the additive inertia identity gives negIndex(D)=negIndex(M)+1. Positive semidefiniteness gives negIndex(M)=0 using the existing positive-index/rank identity and the positive-plus-negative rank partition. The real diagonal sign-count theorem therefore supplies exactly one negative diagonal coordinate at every point. For each coordinate j, the set where d_j is negative is open. Its complement is the union of the other negative-coordinate sets, so it is also closed. Nonemptiness selects one j, and connectedness forces its negative set to be all Y. Every other coordinate is nonnegative everywhere, and a point of Y proves global uniqueness.

Together with StructuredRankOneInertia.inertia_downdate specialized to Matrix.diagonal d, these statements establish both source clauses of Lucid's MO513954 revision 2. Singular matrices, every finite matrix dimension, both signs and all zero multiplicities are retained. There is no extra invertibility, spectral gap, tolerance, compactness or supplied connectedness assumption. This implements the author's proposed block-congruence mechanism and standard Sylvester inertia; no ordinary novelty or global openness claim is made. Public theorem audit registration remains unfinished under issue #25408.

## References

- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneFamily.continuous_family`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneFamily.mo513954_revision2`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneFamily.openSimplex`
- Truth anchor: `D5/S3/QuadraticForms/StructuredRankOneFamily.punctured_simplex_pathConnected`
- Dependency: [D5/S3/QuadraticForms/StructuredRankOneInertia](StructuredRankOneInertia.md)
