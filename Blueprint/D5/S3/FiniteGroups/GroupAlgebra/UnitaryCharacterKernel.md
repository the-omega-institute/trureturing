# Unitary representations and positivity of character kernels

## Abstract

A representation of a monoid by isometries of a finite-dimensional real or complex inner product space is semisimple; a weighted sum of the characters of finitely many representations of a group by isometries is a positive semidefinite kernel when every weight is nonnegative, and for pairwise inequivalent irreducible representations exactly when every weight is nonnegative.

**Theorem 1.1 (Representations by isometries are semisimple).**

$$\forall k \in \operatorname{Type}*,\; \forall G \in \operatorname{Type}*,\; \forall E \in \operatorname{Type}*,\; [\operatorname{RCLike}\left(k\right)], [\operatorname{Monoid}\left(G\right)], [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(k, E\right)], [\operatorname{FiniteDimensional}\left(k, E\right)], \forall \rho \in \operatorname{Representation}\left(k, G, E\right),\; (\forall g \in G,\; \forall v \in E,\; \left\lVert \rho\left(g\right)\left(v\right) \right\rVert = \left\lVert v \right\rVert) \Rightarrow \operatorname{IsSemisimpleRepresentation}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.isSemisimpleRepresentation_of_norm_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gerald B. Folland (2016). *A Course in Abstract Harmonic Analysis*. DOI: [10.1201/b19172](https://doi.org/10.1201/b19172).

*Commentary.*

Let k be the field of real or of complex numbers (an RCLike field), G an arbitrary monoid and E a finite-dimensional inner product space over k. Let rho be a representation of G on E such that every operator rho(g) preserves the norm: the norm of rho(g)(v) equals the norm of v for all g in G and v in E. The statement is that rho is semisimple, that is, every subrepresentation of rho has a complementary subrepresentation. In the displayed formula the arguments in square brackets are the instance hypotheses of the statement. Nothing beyond the monoid axioms is assumed about G: it need not have inverses, it may be infinite, and no topology enters.

Let S be a subrepresentation and let T be the orthogonal complement of its underlying subspace. Fix g in G and write U for rho(g). A linear map that preserves the norm is injective and, by polarization, preserves the inner product. U maps S into S, and its image of S has the dimension of S because U is injective, so in finite dimension U maps S onto S. If v is orthogonal to S and w lies in S, write w = U(w0) with w0 in S; then the inner product of w and U(v) equals the inner product of w0 and v, which is zero. Hence T is invariant under every rho(g) and is a subrepresentation; no inverse in G is used. Because E is finite-dimensional, S and its orthogonal complement are complementary subspaces, so T is a complement of S in the lattice of subrepresentations.

This is the classical complete reducibility of unitary representations. The isometry hypothesis cannot be dropped: the additive group of the integers acting on the plane by n maps (a, b) to (a + n b, b) leaves the line b = 0 invariant, and that line has no invariant complement, since an invariant line spanned by (x, 1) would be mapped to the line spanned by (x + 1, 1).

The statement is used in the decomposition of finite-dimensional unitary representations into irreducible ones: by induction on the dimension, a proper subrepresentation and a complement of it are split off until every summand is irreducible.

**Theorem 1.2 (Character kernels with nonnegative weights are positive semidefinite).**

$$\forall G \in \operatorname{Type}*,\; [\operatorname{Group}\left(G\right)], \forall \iota \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(\iota\right)], \forall W \in \iota \to \operatorname{Type}*,\; [\forall i \in \iota,\; \operatorname{NormedAddCommGroup}\left(W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{InnerProductSpace}\left(\mathbb{C}, W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{FiniteDimensional}\left(\mathbb{C}, W\left(i\right)\right)], \forall \rho \in (\forall i \in \iota,\; \operatorname{Representation}\left(\mathbb{C}, G, W\left(i\right)\right)),\; (\forall i \in \iota,\; \forall g \in G,\; \forall v \in W\left(i\right),\; \left\lVert \rho\left(i\right)\left(g\right)\left(v\right) \right\rVert = \left\lVert v \right\rVert) \Rightarrow \left(\forall c \in \iota \to \mathbb{C},\; (\forall i \in \iota,\; 0 \le c\left(i\right)) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{of}\left(x \mapsto (y \mapsto \sum_{i \in \iota} c\left(i\right) \cdot \operatorname{character}\left(\rho\left(i\right), x \cdot y^{-1}\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.posSemidef_sum_character_kernel_of_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gerald B. Folland (2016). *A Course in Abstract Harmonic Analysis*. DOI: [10.1201/b19172](https://doi.org/10.1201/b19172).

*Commentary.*

Let G be an arbitrary group and iota a finite index type. For each index i, W(i) is a finite-dimensional complex inner product space and rho(i) is a representation of G on W(i) whose operators preserve the norm; no irreducibility and no inequivalence is assumed. Let c(i) be complex weights with 0 <= c(i), where the order on the complex numbers is the one in which a is at most b exactly when b - a is a nonnegative real number. The statement is that the matrix indexed by G x G whose entry at (x, y) is the sum over i of c(i) times the character of rho(i) at x * y^-1 is positive semidefinite: it is Hermitian and its quadratic form is a nonnegative real number on every finitely supported vector. In the formula, of turns this function of x and y into a matrix, and the arguments in square brackets are the instance hypotheses of the statement.

Choose an orthonormal basis e(1), ..., e(d) of each W(i). Since rho(i)(x^-1) preserves the inner product, the character of rho(i) at x * y^-1, which is the trace of rho(i)(x) composed with rho(i)(y^-1), equals the sum over k of the inner products of rho(i)(x^-1)(e(k)) and rho(i)(y^-1)(e(k)). Each such term, as a function of x and y, is the Gram kernel of the vectors rho(i)(x^-1)(e(k)) indexed by x in G, and a Gram kernel indexed by an arbitrary type is positive semidefinite because its quadratic form at a finitely supported vector a is the squared norm of the sum of the a(x) times the corresponding vectors. A combination of positive semidefinite kernels with nonnegative weights is positive semidefinite.

Positivity of the characters of unitary representations is classical in harmonic analysis on groups; the statement here is for an arbitrary group, with no topology, and for a finite family of representations that need not be irreducible.

**Theorem 1.3 (Positive semidefinite character kernels).**

$$\forall G \in \operatorname{Type}*,\; [\operatorname{Group}\left(G\right)], \forall \iota \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(\iota\right)], \forall W \in \iota \to \operatorname{Type}*,\; [\forall i \in \iota,\; \operatorname{NormedAddCommGroup}\left(W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{InnerProductSpace}\left(\mathbb{C}, W\left(i\right)\right)], [\forall i \in \iota,\; \operatorname{FiniteDimensional}\left(\mathbb{C}, W\left(i\right)\right)], \forall \rho \in (\forall i \in \iota,\; \operatorname{Representation}\left(\mathbb{C}, G, W\left(i\right)\right)),\; [\forall i \in \iota,\; \operatorname{IsIrreducible}\left(\rho\left(i\right)\right)], (\forall i \in \iota, j \in \iota,\; i \ne j \Rightarrow \operatorname{IsEmpty}\left(\operatorname{Equiv}\left(\rho\left(i\right), \rho\left(j\right)\right)\right)) \Rightarrow \left((\forall i \in \iota,\; \forall g \in G,\; \forall v \in W\left(i\right),\; \left\lVert \rho\left(i\right)\left(g\right)\left(v\right) \right\rVert = \left\lVert v \right\rVert) \Rightarrow \left(\forall c \in \iota \to \mathbb{C},\; \operatorname{PosSemidef}\left(\operatorname{of}\left(x \mapsto (y \mapsto \sum_{i \in \iota} c\left(i\right) \cdot \operatorname{character}\left(\rho\left(i\right), x \cdot y^{-1}\right))\right)\right) \Leftrightarrow (\forall i \in \iota,\; 0 \le c\left(i\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.posSemidef_sum_character_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gerald B. Folland (2016). *A Course in Abstract Harmonic Analysis*. DOI: [10.1201/b19172](https://doi.org/10.1201/b19172).

*Commentary.*

Let G be an arbitrary group and iota a finite index type. For each index i, W(i) is a finite-dimensional complex inner product space and rho(i) is an irreducible representation of G on W(i) whose operators preserve the norm; rho(i) and rho(j) admit no equivalence of representations when i and j are distinct. Let c(i) be complex weights. The kernel is the matrix indexed by G x G whose entry at (x, y) is the sum over i of c(i) times the character of rho(i) at x * y^-1; in the formula, of turns this function of x and y into a matrix. A matrix indexed by an arbitrary type is positive semidefinite when it is Hermitian and its quadratic form is a nonnegative real number on every finitely supported vector. The statement is that the kernel is positive semidefinite if and only if every weight c(i) is nonnegative; the order on the complex numbers is the one in which a is at most b exactly when b - a is a nonnegative real number. In the displayed formula the arguments in square brackets are the instance hypotheses of the statement.

For nonnegative weights the kernel is positive semidefinite by the preceding theorem, which needs neither irreducibility nor inequivalence `D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.posSemidef_sum_character_kernel_of_nonneg`.

Conversely, suppose the kernel is positive semidefinite and fix an index i. By Burnside's theorem for the family, the families (rho(j)(g))_j, as g ranges over G, span the whole product of the endomorphism algebras End(W(j)) `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.span_range_pi_eq_top`, and inversion is a bijection of G, so there is a finitely supported function b on G for which the sum over y of b(y) times (rho(j)(y^-1))_j is the family that is the identity on W(i) and zero on every other W(j). Because every rho(j)(g) preserves the inner product, its adjoint is rho(j)(g^-1), so the sum over x of the complex conjugate of b(x) times (rho(j)(x))_j is the adjoint family, which is the same family. Expanding the quadratic form of the kernel at b gives the weighted trace pairing of these two families, which is c(i) times the dimension of W(i). An irreducible representation is nonzero, so this dimension is positive and c(i) is nonnegative.

The direction from nonnegative weights to positivity holds for representations by isometries without irreducibility or inequivalence. The converse needs both. On the symmetric group of order two, with sign the nontrivial one-dimensional representation, the reducible representation trivial plus sign and the trivial representation, with weights 1 and -1, give the kernel sign(x) sign(y), which is positive semidefinite although one weight is negative. Two copies of the trivial representation with weights 1 and -1 give the zero kernel. These two examples are not part of the formal statement.

Positivity of characters of unitary representations is classical in harmonic analysis on groups. The converse rests on Burnside's theorem for the family and on the weighted trace pairing; the statement here is for an arbitrary group, with no topology, and for a finite family.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.span_range_pi_eq_top`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.isSemisimpleRepresentation_of_norm_map`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.posSemidef_sum_character_kernel_iff`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.posSemidef_sum_character_kernel_of_nonneg`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.posSemidef_sum_character_kernel_of_nonneg`
- Dependency: [D5/S3/FiniteGroups/FiniteCharacterAlgebra](../FiniteCharacterAlgebra.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank](CharacterKernelRank.md)
