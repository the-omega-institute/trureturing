# Fixed coefficients and diagonal parameters

## Abstract

Irreducibility for the row and diagonal parameter determinants of a fixed matrix.

K is any field and Omega is a finite label type. Every entry of N is fixed. The variables are indexed only by Omega; neither matrix entries nor support edges are independent variables. C is the coefficient embedding and X(Omega) is the family sending each label i to its polynomial variable X(i).

**Definition 1.1 (Row-parameter matrix).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)]  \forall N \in \operatorname{Matrix}\left(Omega, Omega, K\right),\; \operatorname{rowMatrix}\left(N\right) = 1 + \operatorname{diagonal}\left(\operatorname{X}\left(Omega\right)\right) \cdot \operatorname{map}\left(\operatorname{coefficientEmbedding}\left(K, Omega\right), N\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.rowMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix is I plus diag(x) times N. Its determinant has constant coefficient one.

**Definition 1.2 (Fixed matrix plus diagonal parameters).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)]  \forall N \in \operatorname{Matrix}\left(Omega, Omega, K\right),\; \operatorname{diagonalMatrix}\left(N\right) = \operatorname{diagonal}\left(\operatorname{X}\left(Omega\right)\right) + \operatorname{map}\left(\operatorname{coefficientEmbedding}\left(K, Omega\right), N\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.diagonalMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the diagonal parameters vary; every entry of N remains a coefficient.

**Theorem 1.3 (Reciprocal unit coordinates).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)]  \forall N \in \operatorname{Matrix}\left(Omega, Omega, K\right),\; \forall A \in Type,\; [\operatorname{CommRing}\left(A\right)] \forall f \in \operatorname{RingHom}\left(K, A\right),\; \forall x \in \operatorname{Map}\left(Omega, \operatorname{Units}\left(A\right)\right),\; \operatorname{eval}\left(f, \operatorname{values}\left(x\right), \operatorname{det}\left(\operatorname{rowMatrix}\left(N\right)\right)\right) = \operatorname{product}\left(\operatorname{values}\left(x\right)\right) \cdot \operatorname{eval}\left(f, \operatorname{inverseValues}\left(x\right), \operatorname{det}\left(\operatorname{diagonalMatrix}\left(N\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.reciprocal_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

values(x) and inverseValues(x) are the coordinate values of the units x and their inverses. product multiplies those values over all labels. Factoring diag(x) from diag(inverseValues(x))+N gives I+diag(x)N. Taking determinants gives the formula. The product is itself a unit, so the formula applies without introducing a nonunit scalar on the coordinate torus, also over a Laurent polynomial ring.

**Theorem 1.4 (Irreducibility from the actual directed support).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] [\operatorname{Nontrivial}\left(Omega\right)] \forall N \in \operatorname{Matrix}\left(Omega, Omega, K\right),\; (\forall i \in Omega,\; \forall j \in Omega,\; \operatorname{ReflTransGen}\left(\operatorname{nonzeroSupport}\left(N\right), i, j\right)) \Rightarrow (\operatorname{Irreducible}\left(\operatorname{det}\left(\operatorname{rowMatrix}\left(N\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.row_determinant_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

nonzeroSupport(N) has an edge from i to j exactly when N(i,j) is nonzero. ReflTransGen permits any finite directed path, including length zero. Nontrivial Omega means at least two labels. No order, positivity, characteristic, generic position or restriction on the coefficients is assumed.

Differentiate the matrix-adjugate identity entrywise. A zero adjugate entry forces the product of the two adjugate entries on every two-step route to vanish. Evaluation at x=0 gives the identity adjugate; differentiating there shows that every nonzero off-diagonal coefficient gives a nonzero adjugate entry. Induction along a directed path proves all required adjugate entries are nonzero. The adjugate column with its own row removed is independent of that row parameter. This identifies each determinant derivative and makes every two-parameter Rayleigh difference nonzero. The determinant is multiaffine, so factors would have disjoint variable sets; parameters selected from opposite nonconstant factors would have zero Rayleigh difference, a contradiction.

The fixed-matrix irreducibility criterion is classical; compare Al Ahmadieh, The Fiber of the principal minor map, arXiv:2309.00806v2, Lemmas 2.2, 4.2 and 5.1. This proof supplies its row-scaled form directly. An identification with the original multiplication obstruction polynomial requires its original basis and normalization correspondence.

**Theorem 1.5 (Irreducibility of the diagonal-plus-fixed-matrix determinant).**

$$\forall K \in Type,\; \forall Omega \in Type,\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(Omega\right)] [\operatorname{DecidableEq}\left(Omega\right)] [\operatorname{Nontrivial}\left(Omega\right)] \forall N \in \operatorname{Matrix}\left(Omega, Omega, K\right),\; (\forall i \in Omega,\; \forall j \in Omega,\; \operatorname{ReflTransGen}\left(\operatorname{nonzeroSupport}\left(N\right), i, j\right)) \Rightarrow (\operatorname{Irreducible}\left(\operatorname{det}\left(\operatorname{diagonalMatrix}\left(N\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.diagonal_determinant_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embed the polynomial ring in its fraction field, where every coordinate X(i) is a unit. The reciprocal matrix identity and the multiplicative adjugate identity transfer every nonzero adjugate entry along the directed support from the row matrix to the diagonal matrix. Differentiating with respect to y(i) now inserts the elementary diagonal matrix at i, so a two-parameter Rayleigh difference is the product of the two opposite adjugate entries. It is nonzero. Multiaffinity again forces the variables of any two nonconstant factors to be disjoint, contradicting that Rayleigh difference. This proves the fixed matrix criterion over every field in every size at least two.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.diagonalMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.diagonal_determinant_irreducible`
- Truth anchor: `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.reciprocal_determinant`
- Truth anchor: `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.rowMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/FixedDiagonalDeterminant.row_determinant_irreducible`
