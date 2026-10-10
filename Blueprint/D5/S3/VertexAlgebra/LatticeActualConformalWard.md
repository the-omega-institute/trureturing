# Full Integer Ward Law on Every Actual State

## Abstract

Actual conformal actions truncate before binomial weighting and satisfy every integer Ward law.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

H remains arbitrary. For every integer m,q and every actual state a define wardTerm(j)=choose(m+1,j) (Y(L_(j-1)a))_(m+q+1-j), where omega_j a=L_(j-1)a. Their finite support follows directly from the released Sugawara-field truncation and its mode convention, before binomial multiplication. Higher conformal actions are retained.

**Theorem 1.1 (Full Ward identity at all integer modes).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualConformalWard.ward_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualConformalWard.ward_commutator` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

[L_m,(Y(a))_q]=sum_(j>=0) choose(m+1,j) (Y(L_(j-1)a))_(m+q+1-j). This follows from the genuine actual mode commutator with omega and the actual Sugawara coefficient convention. It requires no inverse or eigenvector premise and does not impose a primary-state formula on arbitrary states.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, supplies residue locality and reconstruction by creative local fields, divided derivatives and nested normal products.

The consumed Sugawara normal-ordering and commutator architecture retains Kalle Kytola, VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4, Apache-2.0 attribution. The actual carrier and matrix contractions are explicit. The complete Virasoro theorem is a separately delivered supplier; these state laws do not replace it with a partial proof.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualConformalWard.ward_commutator`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateDerivative](LatticeActualStateDerivative.md)
