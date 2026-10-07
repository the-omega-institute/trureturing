# Actual Fields of Every Lattice State

## Abstract

Actual fields of every lattice state are creative and translation covariant.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

For a charge delta and occurrence word, wordField starts with the actual charged ground field and right-nests normalMinusOne of each divided current derivative. The occurrences of a monomial are e.toMultiset.toList; their multiset and product are proved. Monomial basis extension gives polynomialField, and Finsupp.lsum over the finite charge support gives Y. Every recursive field is already lower truncated.

Word induction evaluates both finite normal-product branches on the actual vacuum. Divided derivatives create the correct oscillator variable, while nonnegative vacuum coefficients vanish. Binomial covariance and finite linear extension then transport the same actual T to every word and every state.

**Theorem 1.1 (Creation on every actual state).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_creation` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every a in V, (Y(a))_(-1) vacuum=a. No reconstruction or locality premise is used.

**Theorem 1.2 (All nonnegative vacuum modes vanish).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_creativity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_creativity` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every a in V and every integer q>=0, (Y(a))_q vacuum=0. The proof evaluates the two normal-product sums on each word and extends over finite supports.

**Theorem 1.3 (Actual translation covariance).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_covariance` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every a and integer q, [T,(Y(a))_q]=-q (Y(a))_(q-1). The current and charged generator covariance is consumed, and divided-derivative binomial shifts and normal-product covariance give the unrestricted state law.

**Theorem 1.4 (The actual vacuum field is the identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_vacuum` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Y(vacuum)=identityField. The zero charged exponential and translated polynomial are evaluated, with identity mode -1 and all other modes zero.

**Theorem 1.5 (Exact finite state-field expansion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_expansion` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Y(a) is the sum over the finite charge support and the finite monomial basis support, with the actual polynomial coefficients multiplying the corresponding wordField. It retains every charge and oscillator occurrence.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, supplies residue locality and reconstruction by creative local fields, divided derivatives and nested normal products.

Finite normal-product and integer residue kernels retain Scott Carnahan attribution: vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, VertexAlg/VertexBasic/VertexOperator.lean, Apache-2.0. Actual coefficient proofs are re-elaborated on V; no polynomial Fock theorem is transferred between carriers.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_creation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_creativity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeAllStateField.stateField_vacuum`
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProduct](FieldNormalProduct.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](LatticeSugawaraConformal.md)
