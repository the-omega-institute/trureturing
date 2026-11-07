# Frobenius-equivariant Cholesky bijections

## Abstract

Finite arithmetic recipes give rank-preserving Frobenius-equivariant bijections between upper triangular square-zero matrices and zero Gram roots.

**Definition 1.1 (The finite-field question).**

$$\operatorname{claim} = (\forall (e : \mathbb{N}), (1 \le e) \Rightarrow (\forall (n : \mathbb{N}), \exists (p : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \operatorname{Recipe}(n))), \forall (F : \operatorname{Type}), [\operatorname{Field}(F)], [\operatorname{Fintype}(F)], [\operatorname{DecidableEq}(F)], [\operatorname{CharP}(F, 2)], (\operatorname{Fintype}.\operatorname{card}(F) = 2^{e}) \Rightarrow ((\operatorname{Set}.\operatorname{BijOn}((\operatorname{fun} (X : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), F)) \mapsto \operatorname{Matrix}.\operatorname{map}(p, \operatorname{Recipe}.\operatorname{eval}(X))), \operatorname{B}(F, n), \operatorname{C}(F, n))) \land (\forall (X : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), F)), (X \in \operatorname{B}(F, n)) \Rightarrow (\operatorname{Matrix}.\operatorname{rank}(\operatorname{Matrix}.\operatorname{map}(p, \operatorname{Recipe}.\operatorname{eval}(X))) = \operatorname{Matrix}.\operatorname{rank}(X))) \land (\forall (X : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), F)), (X \in \operatorname{B}(F, n)) \Rightarrow (\operatorname{Matrix}.\operatorname{map}(p, \operatorname{Recipe}.\operatorname{eval}(\operatorname{Matrix}.\operatorname{map}(X, \operatorname{frobenius}(F, 2)))) = \operatorname{Matrix}.\operatorname{map}(\operatorname{Matrix}.\operatorname{map}(p, \operatorname{Recipe}.\operatorname{eval}(X)), \operatorname{frobenius}(F, 2)))))))$$

*Formalization.* `D5/S3/QuadraticForms/FrobeniusCholeskyResult.claim` (`✓ std3`).

*Citation.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

Wu and Zhou, Singular Cholesky Fibers over Finite Fields, arXiv:2609.00533v1, Section 8(iv), p. 43: “Over $\mathbb{F}_{2^{e}}$, find a version of the rank-preserving bijection that is Frobenius equivariant and avoids the RREF–lexicographic choice. This would strengthen the present flag-compatible construction without changing its rank behavior.” Here B(F,n) consists of upper triangular X with X * X = 0, and C(F,n) consists of upper triangular U with transpose(U) * U = 0. Fin n indexes both rows and columns; n = 0 includes the empty matrix. A single matrix p of Recipe n works over every field presentation with the specified cardinality. Frobenius acts entrywise by x mapped to x squared.

**Theorem 1.2 (Uniform rank-preserving arithmetic construction).**

$$\forall (e : \mathbb{N}), (1 \le e) \Rightarrow (\forall (n : \mathbb{N}), \exists (p : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \operatorname{Recipe}(n))), \forall (F : \operatorname{Type}), [\operatorname{Field}(F)], [\operatorname{Fintype}(F)], [\operatorname{DecidableEq}(F)], [\operatorname{CharP}(F, 2)], (\operatorname{Fintype}.\operatorname{card}(F) = 2^{e}) \Rightarrow ((\operatorname{Set}.\operatorname{BijOn}((\operatorname{fun} (X : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), F)) \mapsto \operatorname{Matrix}.\operatorname{map}(p, \operatorname{Recipe}.\operatorname{eval}(X))), \operatorname{B}(F, n), \operatorname{C}(F, n))) \land (\forall (X : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), F)), (X \in \operatorname{B}(F, n)) \Rightarrow (\operatorname{Matrix}.\operatorname{rank}(\operatorname{Matrix}.\operatorname{map}(p, \operatorname{Recipe}.\operatorname{eval}(X))) = \operatorname{Matrix}.\operatorname{rank}(X))) \land (\forall (X : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), F)), (X \in \operatorname{B}(F, n)) \Rightarrow (\operatorname{Matrix}.\operatorname{map}(p, \operatorname{Recipe}.\operatorname{eval}(\operatorname{Matrix}.\operatorname{map}(X, \operatorname{frobenius}(F, 2)))) = \operatorname{Matrix}.\operatorname{map}(\operatorname{Matrix}.\operatorname{map}(p, \operatorname{Recipe}.\operatorname{eval}(X)), \operatorname{frobenius}(F, 2))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/FrobeniusCholeskyResult.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hongfeng Wu; Kai Zhou (2026). *Singular Cholesky Fibers over Finite Fields*. URL: <https://arxiv.org/abs/2609.00533v1>.

*Commentary.*

The proof selects nonzero minors using only coordinate indices and zero tests. Free-coordinate kernel vectors extend independent image columns to adapted kernel frames. Coordinate transport between the two frames is bijective and preserves membership in the old image.

The recursion transports the final column and makes the final diagonal its coordinate sum. In characteristic two the square of that sum equals the sum of coordinate squares. This gives the zero Gram equation and uniqueness of the final diagonal. Membership of the new column in the old image determines the rank increase on both sides.

The arithmetic recipe contains no field-element ordering or enumeration. The supporting construction works over every characteristic-two field. Arbitrary coordinate-change naturality and a separately assembled theorem for all field embeddings and leading-principal truncations remain additional questions.

## References

- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyResult.claim`
- Truth anchor: `D5/S3/QuadraticForms/FrobeniusCholeskyResult.result`
- Dependency: [D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis](../Estimation/ExperimentCost/MinimumCostRoleBasis.md)
- Dependency: [D5/S3/QuadraticForms/FrobeniusCholeskyLinear](FrobeniusCholeskyLinear.md)
- Dependency: [D5/S3/QuadraticForms/FrobeniusCholeskyRecipes](FrobeniusCholeskyRecipes.md)
- Dependency: [D5/S3/QuadraticForms/FrobeniusCholeskyRecursion](FrobeniusCholeskyRecursion.md)
