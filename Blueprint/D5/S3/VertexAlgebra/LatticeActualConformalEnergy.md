# Actual Nonhomogeneous, Weighted and Fused Energy Laws

## Abstract

The two inverse-Gram identities give nonhomogeneous, weighted and fused actual energy laws.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

Write Gc=gramComplex(D). Assume exactly H*Gc=1 and Gc*H=1 with ordinary matrix multiplication. There is no separate symmetry, positivity, grading or desired energy hypothesis. The one-mode commutator with omega, actual L_(-1)=T, and unconditional state differentiation give the energy identity on arbitrary states, including sums with different charges or energies.

**Theorem 1.1 (Nonhomogeneous energy covariance).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.energy_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.energy_covariance` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every actual a and integer q, [L_0,(Y(a))_q]=(Y(L_0 a))_q -(q+1)(Y(a))_q, under the stated inverse pair.

**Theorem 1.2 (Explicit actual eigenstate specialization).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.eigenstate_mode_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.eigenstate_mode_energy` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Assume additionally ha: L_0 a=energy*a. Then [L_0,(Y(a))_q]=(energy-q-1)(Y(a))_q. The actual eigenvalue premise is explicit; it is not inferred for an arbitrary state.

**Theorem 1.3 (Weighted charged polynomial specialization).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.weighted_homogeneous_mode_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.weighted_homogeneous_mode_energy` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For beta a charge and p weighted homogeneous of natural degree r with weights (i,n) to n+1, the actual supplier proves L_0 single(beta,p)=(r+B(beta,beta)/2) single(beta,p). Consequently its q-mode commutator has scalar r+B(beta,beta)/2-q-1. This uses the actual weighted polynomial premise, not a finite grading.

**Theorem 1.4 (General actual mode-product energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.fused_state_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.fused_state_energy` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary a,b and integer q, L_0 mu(a,q,b)=mu(L_0 a,q,b)+mu(a,q,L_0 b)-(q+1)mu(a,q,b). Evaluating nonhomogeneous energy covariance on b proves the law; neither state needs to be an eigenvector.

**Theorem 1.5 (Both explicit eigenstate premises give fused energy).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.fused_eigenstate_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.fused_eigenstate_energy` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Assume ha: L_0 a=alpha*a and hb: L_0 b=beta*b, in addition to the same two inverse equations. Then L_0 mu(a,q,b)=(alpha+beta-q-1)mu(a,q,b). Both eigenvalue premises are retained in the exact public telescope.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, supplies residue locality and reconstruction by creative local fields, divided derivatives and nested normal products.

The consumed Sugawara normal-ordering and commutator architecture retains Kalle Kytola, VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4, Apache-2.0 attribution. The actual carrier and matrix contractions are explicit. The complete Virasoro theorem is a separately delivered supplier; these state laws do not replace it with a partial proof.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.eigenstate_mode_energy`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.energy_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.fused_eigenstate_energy`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.fused_state_energy`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualConformalEnergy.weighted_homogeneous_mode_energy`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalWard](LatticeActualConformalWard.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](LatticeSugawaraConformal.md)
