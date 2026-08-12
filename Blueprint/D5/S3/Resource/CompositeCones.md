# The Inclusion Chain of Composite Matrix Cones

## Abstract

For finite complex matrices, separable, positive-semidefinite, and block-positive cones form a proved inclusion chain.

For a bipartite finite-dimensional system there are three nested cones of finite complex matrices: separable, positive semidefinite, and block positive, where block positivity means nonnegativity on every product vector. Separability is the strongest condition and block positivity the weakest.

This module proves only the two inclusions; neither inclusion is proved proper, and no witness is exhibited. The source atom writes proper-inclusion symbols, but this formalization does not establish that a positive semidefinite matrix can fail to be separable or that a block-positive matrix can fail to be positive semidefinite.

The first inclusion follows because a Kronecker product of positive semidefinite factors is positive semidefinite and a finite sum of such matrices remains positive semidefinite. The second is weaker because block positivity tests the quadratic form only on the smaller set of product vectors, whereas positive semidefiniteness gives nonnegativity on every vector.

The proof reuses the library lemmas Matrix.PosSemidef.kronecker, Matrix.posSemidef_sum, and Matrix.PosSemidef.re_dotProduct_nonneg; these library-search results are recorded in the Lean source rather than reproved locally. No physical interpretation involving entanglement, witnesses, or separability testing is asserted.

**Definition 1.1 (The separable cone is a finite sum of PSD Kronecker products).**

$$\operatorname{separableCone}(W)\Leftrightarrow \exists k\in \mathbb{N}, \exists A, \exists B, (\forall i, \operatorname{PosSemidef}(A(i)) \land \operatorname{PosSemidef}(B(i))) \land W=\sum i \in \operatorname{Fin}(k) A(i)\times B(i))$$

*Formalization.* `D5/S3/Resource/CompositeCones.separableCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A matrix belongs to the separable cone exactly when some finite family of positive semidefinite matrices A and B represents it as the sum over Fin k of their Kronecker products. The index size k may be zero.

**Definition 1.2 (Block positivity tests every product vector).**

$$\operatorname{blockPositive}(W)\Leftrightarrow \forall a, b, 0\leq \operatorname{Re}(\operatorname{dotProduct}(a\times b, W(a\times b)))$$

*Formalization.* `D5/S3/Resource/CompositeCones.blockPositive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A matrix is block positive when the real part of its quadratic form is nonnegative on every vector formed pointwise from a vector a on the first finite index set and a vector b on the second.

**Theorem 1.3 (Separable matrices are positive semidefinite).**

$$\forall m, n, W, \operatorname{separableCone}(W) \Rightarrow \operatorname{PosSemidef}(W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeCones.separable_isPosSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every separable matrix is positive semidefinite. The proof applies the Kronecker-product lemma to each pair of PSD factors and then the finite-sum lemma to the resulting family.

**Theorem 1.4 (Positive semidefinite matrices are block positive).**

$$\forall m, n, W, \operatorname{PosSemidef}(W) \Rightarrow \operatorname{blockPositive}(W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/CompositeCones.posSemidef_blockPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite matrix is block positive because its quadratic form has nonnegative real part on all vectors, hence on the special product vectors used by the block-positive definition.

## References

- Truth anchor: `D5/S3/Resource/CompositeCones.blockPositive`
- Truth anchor: `D5/S3/Resource/CompositeCones.posSemidef_blockPositive`
- Truth anchor: `D5/S3/Resource/CompositeCones.separableCone`
- Truth anchor: `D5/S3/Resource/CompositeCones.separable_isPosSemidef`
