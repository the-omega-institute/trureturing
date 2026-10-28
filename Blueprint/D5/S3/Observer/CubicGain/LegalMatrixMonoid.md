# The exact legal matrix monoid

## Abstract

Native forward words coincide with all nonnegative integral matrices of determinant plus or minus one.

Mat is the full real 2 by 2 matrix space, and i,j range over Fin 2, displayed as {0,1}. A Boolean word u is a finite chronological list: false selects M=[[0,1],[1,1]], true selects J=[[0,1],[1,0]], and its head acts first. Write T(u)=futureProduct(u). The existing recursion is T([])=I and T(e::u)=T(u)E(e). In particular chronological M,J has matrix JM=U=[[1,1],[0,1]], while chronological J,M has matrix MJ=L=[[1,0],[1,1]].

**Lemma 1.1 (Concatenation executes the earlier word first).**

$$\forall u,v, \operatorname{T}(u++v)= \operatorname{T}(v)\operatorname{T}(u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LegalMatrixMonoid.product_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite words u,v, including empty words, chronological concatenation gives T(u++v)=T(v)T(u). Induction on u follows the existing product recursion and matrix associativity. This identity relates the actual cumulative endpoints and also cancels the adjacent J pairs when every multiplier is conjugated.

**Theorem 1.2 (Exact forward-word characterization).**

$$\forall H\in \mathbb{R}^{2\times2}, (\exists u\in \{0,1\}^{*}, \operatorname{T}(u)= H)\iff (\forall i,j\in \{0,1\}, (0\leq H_{ij}\land \exists z\in \mathbb{Z}, H_{ij}= z))\land (\operatorname{det}(H)= 1\lor \operatorname{det}(H)= -1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LegalMatrixMonoid.legal_matrix_monoid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real matrix H is included in the displayed equivalence. The right side says each entry is nonnegative and is the real cast of an integer, and the determinant is either 1 or -1. The left side supplies an actual finite list of native forward actions. There are no entry or word-length bounds. I is represented by the empty list, J by [true], and matrices with zero entries are retained.

For every word, induction constructs a natural four-entry matrix whose real cast is exactly its existing product T(u). Matrix multiplication commutes with this cast. This proves integrality and nonnegativity of the actual product. Both native factors have determinant -1, so every finite product has one of the two determinant signs.

Conversely, nonnegative integral real entries have natural representatives. At determinant 1, the natural matrix generation theorem constructs an L/U word. Replacing each factor by its chronological native pair gives exactly the real product, with reversal handled by T(u++v)=T(v)T(u). At determinant -1, exchange the rows to obtain determinant 1, construct its word, then append J to exchange them back. All subtractions occur only in the natural parent proof. The acquired word contains M and J alone.

The characterization supplies the monoid step used by exact cumulative continuation and by later legal-prefix normal forms. Those conclusions, their rank conditions and their additional endpoint filters are not asserted here.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/LegalMatrixMonoid.legal_matrix_monoid`
- Truth anchor: `D5/S3/Observer/CubicGain/LegalMatrixMonoid.product_append`
- Dependency: [D5/S3/Observer/CubicGain/CommonWordSensitivity](CommonWordSensitivity.md)
- Dependency: [D5/S3/PrimeForms/SternBrocot/UnimodularGeneration](../../PrimeForms/SternBrocot/UnimodularGeneration.md)
