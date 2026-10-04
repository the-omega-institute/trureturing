# Charged Polynomial Fock Field Coefficients

## Abstract

Every charged polynomial Fock field coefficient is a finite sum over positional deletions.

Let F=C[X_0,X_1,...] be the complex polynomial Fock space. The actual current J has mode -j-1 equal to multiplication by X_j, mode zero equal to zero, and mode j+1 equal to (j+1) times partial differentiation in X_j, for every natural j. Normalized mode n means Laurent power -n-1. The divided derivative D_j is 1/j! times the ordinary formal derivative.

**Definition 1.1 (The current of arbitrary complex charge).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedCurrent`

*Formalization.* `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedCurrent` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *A Note on Free Bosonic Vertex Algebra and its Conformal Vectors*. URL: <https://arxiv.org/abs/hep-th/9704060v1>.

*Commentary.*

For every complex lambda, chargedCurrent(lambda) is J plus the singleton Laurent field lambda z^(-1) id_F. Its normalized mode zero is lambda id_F, and every other normalized mode is the corresponding actual current mode. The sum is a field using J's lower truncation and the singleton's support.

**Definition 1.2 (Right-nested ordered word fields).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedWordField`

*Formalization.* `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedWordField` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For every complex lambda and finite natural word w, set W_lambda([])=identityField and W_lambda(j::w)=N(D_j chargedCurrent(lambda),W_lambda(w)), where N(A,B) is the existing ordered minus-one normal product. At integer mode n on input v its two branches are the pointwise finite sums over natural k of A_(-k-1) B_(n+k) v and B_(n-k-1) A_k v. This specifies the right nesting and the divided-derivative normalization.

**Definition 1.3 (The monomial basis extension).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedY`

*Formalization.* `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedY` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *A Note on Free Bosonic Vertex Algebra and its Conformal Vectors*. URL: <https://arxiv.org/abs/hep-th/9704060v1>.

*Commentary.*

For every complex lambda, chargedY(lambda) is the complex linear map obtained from the existing basisMonomials(N,C) by assigning exponent e the field W_lambda(occurrences(e)). The existing occurrences(e) is the sorted list e.toMultiset.sort. Thus every polynomial is extended by its actual monomial coefficients.

For a finite natural word w, let P(w)=Fin(length(w)). For each subset R of P(w), keep(w,R) is List.finRange(length(w)) filtered to positions outside R and then mapped by w.get. Set s(w,R)=sum over i in R of (w.get(i)+1), as an integer, and c(lambda,w,R)=product over i in R of ((-1)^(w.get(i)) lambda), as a complex number. The empty sum is zero and the empty product is one, for every lambda. Masks distinguish repeated labels, and keep preserves both repetitions and relative order.

**Theorem 1.4 (Every input polynomial and every integer mode).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.charged_statefield_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.charged_statefield_coefficients` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *A Note on Free Bosonic Vertex Algebra and its Conformal Vectors*. URL: <https://arxiv.org/abs/hep-th/9704060v1>.

*Commentary.*

For every complex lambda, all u,v in F and every integer n, chargedY(lambda)(u)_n v equals the sum over e in the finite support of u and over every R in the powerset of the universal finite set P(occurrences(e)) of (coeff(e,u) c(lambda,occurrences(e),R)) acting by complex scalar multiplication on wordField(keep(occurrences(e),R))_(n-s(occurrences(e),R)) v. Here wordField is the existing zero-charge ordered word field, acting on the same arbitrary input v. There are no further hypotheses on the charge, polynomials or mode.

The divided derivative of the singleton has only normalized mode j, with value (-1)^j lambda id_F. No factorial remains. It gives no correction in the negative branch, and its positive branch selects k=j and contributes (-1)^j lambda times the tail mode n-j-1. Word induction applies at every integer mode and to every input, including the actual derivative modes of the charged current applied to that input.

Before sums are rearranged, each original branch and every separate transformed mask summand has finite support. Increasing right modes vanish on the fixed input in the forward branch. Increasing left modes vanish on that input in the reverse branch. For a transformed mask the forward bound uses the Laurent order of its retained word at the shifted mode; the reverse bound uses the left field on the original input. Their finite union justifies the exchanges. Every parent mask is uniquely a successor image of a tail mask or that image with position zero inserted. These alternatives preserve or remove the first label and give exactly the displayed weights and shifts.

An empty word has only the empty mask. Its field is the identity, whose mode -1 is id_F and whose other integer modes are zero. A zero polynomial has empty support. Empty masks, full masks, zero charge, repeated labels and all mode signs are included in the same equality.

Matsuo-Nagatomo's free-boson Sections 2.2-2.3 supply the polynomial mode conventions, and their locality Sections 1.2-1.4 supply the normalized coefficients, divided derivatives and residue conventions. These references provide background for the specified finite coefficient expansion; no mathematical novelty is asserted. Charged-module Jacobi, fusion, a Monster realization, complete string theory and AdS/CFT spacetime dynamics remain beyond this coefficient equality.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedWordField`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.chargedY`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockChargedStateField.charged_statefield_coefficients`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockChargedIrreducibility](PolynomialFockChargedIrreducibility.md)
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockStateField](PolynomialFockStateField.md)
