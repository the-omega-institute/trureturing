# Actual Charged Locality and Zero-Rank Cases

## Abstract

Actual charged fields are mutually local for every ordinary even lattice, including rank zero.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

Evaluate the actual charged commutator on each charge-polynomial input. The two ordered products and cocycle skew reduce it to the bounded common kernel discrepancy. Finite signed Pascal cancellation kills it at (-B(alpha,beta)).toNat. Normalized delta corresponds to rawDelta under the actual Laurent index -m-1, and Finsupp extensionality gives all inputs.

**Theorem 1.1 (Uniform locality of actual charged fields).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualChargedLocality.actual_charged_charged_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualChargedLocality.actual_charged_charged_locality` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all alpha,beta, delta iterated (-B(alpha,beta)).toNat kills the actual field commutator. The exponent is independent of the input vector. This is a sufficient exact stated order; no claim that it is always minimal is needed.

**Theorem 1.2 (Rank zero satisfies the same actual law).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualChargedLocality.rank_zero_actual_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualChargedLocality.rank_zero_actual_locality` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Under D.rank=0 every charge is zero. The actual zero field is the identity and its commutator vanishes, with the same exponent formula equal to zero.

**Theorem 1.3 (Nonnegative pairing gives commutation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualChargedLocality.nonnegative_pairing_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualChargedLocality.nonnegative_pairing_commutator` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

If B(alpha,beta)>=0, the stated exponent is zero and the coefficient commutator itself is zero.

**Theorem 1.4 (Coincident charges retain the actual cocycle parity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualChargedLocality.diagonal_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualChargedLocality.diagonal_locality` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every alpha, B(alpha,alpha) is even and the same charged locality law holds at alpha=beta, with no distinct-charge premise.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualChargedLocality.actual_charged_charged_locality`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualChargedLocality.diagonal_locality`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualChargedLocality.nonnegative_pairing_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualChargedLocality.rank_zero_actual_locality`
- Dependency: [D5/S3/VertexAlgebra/BinomialKernelDelta](BinomialKernelDelta.md)
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProductLocality](FieldNormalProductLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualOrderedProducts](LatticeActualOrderedProducts.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
