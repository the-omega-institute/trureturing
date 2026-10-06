# Actual Neutral Current Algebra and Locality

## Abstract

Actual neutral modes satisfy the Heisenberg commutator and uniform order-two locality.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

On single(delta,p), negative current modes multiply by oscillator variables, the zero mode is B(e_i,delta), and positive mode m is m times the Gram-weighted partial derivative at frequency m-1. Partial derivatives commute. Their mixed multiplication commutator supplies the central term, on every charge sector.

**Theorem 1.1 (All-sector actual Heisenberg commutator).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra.neutral_heisenberg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra.neutral_heisenberg` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all i,j and integer m,n, [h_i(m),h_j(n)]=m G_ij delta(m+n,0) id. The proof covers both mixed sign branches, the zero charge scalars, and equal-sign commutation; it uses no inverse matrix.

**Theorem 1.2 (Uniform neutral locality of order two).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra.actual_neutral_neutral_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra.actual_neutral_neutral_locality` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every i,j, delta iterated twice kills the coefficient commutator of the actual neutral fields. The Heisenberg formula at the three shifted index pairs has equal central support and cancelling scalar coefficients.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra.actual_neutral_neutral_locality`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra.neutral_heisenberg`
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProductLocality](FieldNormalProductLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualGeneratorLocality](LatticeActualGeneratorLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
