# Actual Current Derivations and Creation Exponentials

## Abstract

Current derivations act on actual creation exponentials and translated polynomials.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

The consumed coefficientwise series derivation obeys Leibniz and commutes with formal differentiation. The difference between d(exp(S)) and exp(S)d(S) has zero constant term and satisfies the same first-order differential equation. Strong induction on finite antidiagonals makes every coefficient zero.

**Theorem 1.1 (Coefficientwise chain rule for the actual exponential).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualAnnihilation.actual_exponential_derivation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualAnnihilation.actual_exponential_derivation` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every complex-linear polynomial derivation d and actual creation charge alpha, seriesDerivation(d,creationExponential(alpha)) equals creationExponential(alpha) times seriesDerivation(d,creationSeries(alpha)). No annihilation formula is assumed.

**Theorem 1.2 (Exact current action on every integer creation coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_creation` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The Gram-weighted derivative at frequency k sends creationCoeff(alpha,t) to (k+1)^(-1) B(e_i,alpha) creationCoeff(alpha,t-(k+1)). Negative t and the integer-to-natural boundary are proved explicitly.

**Theorem 1.3 (Annihilation commutes with actual polynomial translation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_transport` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every oscillator polynomial p the translated annihilation equals the coefficientwise polynomial derivation of translatedPolynomial(alpha,p). Polynomial induction proves this at each variable, sum and product.

**Theorem 1.4 (The finite convolution derivative includes the charge shift).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_convolution` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Differentiating the actual convolution gives its differentiated polynomial input plus (k+1)^(-1) B(e_i,alpha) times the convolution at s-(k+1). This is the consumed positive-current step of the mixed commutator.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualAnnihilation.actual_exponential_derivation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_convolution`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_creation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_transport`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](LatticeActualProductKernel.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality](LatticeGeneratingFieldLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraCurrents](LatticeSugawaraCurrents.md)
