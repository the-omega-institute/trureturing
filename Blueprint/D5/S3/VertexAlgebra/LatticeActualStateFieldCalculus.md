# Actual Mode Commutators and Normal State Products

## Abstract

Actual Borcherds and residue identities give mode commutators and normal state products.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

Actual nonnegative state products truncate by the Hahn order before multiplication by any binomial. Borcherds at r=0 then gives the complete mode commutator. The residue iterate at -1 identifies the actual state product with the normal field product, after computing (-1)^j choose(-1,j)=1.

**Theorem 1.1 (Inner actual states truncate first).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.nonnegative_products_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.nonnegative_products_finite` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For arbitrary a,b, j to mu(a,j,b) has finite support. The proof uses the lower Hahn order of Y(a)b; no positive binomial upper bound is assumed.

**Theorem 1.2 (Every integer mode commutator).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.mode_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.mode_commutator` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

[a_p,b_q] is the finite sum over j>=0 of choose(p,j) (Y(mu(a,j,b)))_(p+q-j), for all integer p,q. The inner-state support controls the endomorphism sum, including negative p.

**Theorem 1.3 (Actual minus-one state product is a normal product).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.minus_one_product_field`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.minus_one_product_field` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Y(mu(a,-1,b))=normalMinusOne(Y(a),Y(b)).operator. At mode q on c the complete two finite sums are sum_j a_(-j-1)(b_(q+j)c) and sum_j b_(q-j-1)(a_j c). The formula follows from the proved iterate and is not a definition or compatibility premise.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, supplies residue locality and reconstruction by creative local fields, divided derivatives and nested normal products.

Finite normal-product and integer residue kernels retain Scott Carnahan attribution: vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, VertexAlg/VertexBasic/VertexOperator.lean, Apache-2.0. Actual coefficient proofs are re-elaborated on V; no polynomial Fock theorem is transferred between carriers.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.minus_one_product_field`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.mode_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.nonnegative_products_finite`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualVertexAlgebra](LatticeActualVertexAlgebra.md)
