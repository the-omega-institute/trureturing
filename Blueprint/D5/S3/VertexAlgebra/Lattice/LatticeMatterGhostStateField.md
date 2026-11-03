# The Original All-State Matter/Ghost Field

## Abstract

Original all-state matter and ghost fields have locally finite tensor coefficients and signed locality.

The carrier is the original algebraic LatticeMatterGhostCoupling.State D: the finite-charge lattice polynomial carrier tensor CountableOccupationFock.Fock over C. The construction uses the original LatticeAllStateField.Y and BcGhostStateField.Y. Normalized mode n is raw Laurent power -n-1. No endomorphism family is assumed globally finite.

**Theorem 1.1 (The literal locally finite tensor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.tensor_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.tensor_coefficients` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For any D, matter states u,v, ghost states a,b, integer n and actual tail bounds M,G, the coefficient is the finsum over k of Ym(u)[[k]]v tensor Yg(a)[[n-1-k]]b. Its support lies in n-G <= k <= M-1 and n >= M+G kills it.

**Theorem 1.2 (All original algebraic states and inputs truncate).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_truncation` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original tensor field state s and original algebraic input x, one integer N kills every normalized mode n >= N. The construction descends through both tensor relations using pointwise finite support.

**Theorem 1.3 (The original vacuum and all-state creation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_vacuum_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_vacuum_creation` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Y(vacuum) is the identity field, mode -1 on the vacuum creates every state, every nonnegative vacuum coefficient vanishes, and the original tensor translation kills the vacuum.

**Theorem 1.4 (The actual translation acts on every coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_covariance` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The tensor sum of original matter translation and original ghost L(-1) has commutator with mode n equal to -n times mode n-1, for every original field state.

**Theorem 1.5 (Original ghost parity acts on the full field).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_parity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_parity` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Identity on matter tensor the actual occupation parity intertwines every coefficient with the coefficient of the parity-transformed field state.

**Theorem 1.6 (The genuine coupled conformal state has the actual modes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.conformal_modes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.conformal_modes` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite rank including zero, arbitrary complex matrix H and integer m, the coefficient m+1 of omega_m tensor vac_g plus vac_m tensor Omega_g is matterMode(D,H,m) + ghostVirasoro(D,m). No inverse-Gram or rank-26 assumption occurs.

**Theorem 1.7 (The literal coupled current has the original total charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.current_zero_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.current_zero_mode` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D and arbitrary complex H, mode zero of omega_m tensor ket{1} plus vac_m tensor Jg equals LatticeBRST.totalCharge(D,H). The exact integer reindex m=k-1 identifies the original matter coupling T, and the ghost term is the original anomalous Qg.

**Theorem 1.8 (Signed locality has an actual finite-support proof).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_locality` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary algebraic homogeneous field states of parities p,q, one order N kills their signed discrepancy under delta(p,q)=f(p+1,q)-f(p,q+1). Only same-order pair families are summed before clearing the two factor polynomials. The cleared factors have rectangular support, so finite convolution permits substitution of both locality identities. Mixed-order infinite-support rays remain allowed.

The vacuum cuts are original: b_p creates exactly for p <= -2 and c_q creates exactly for q <= 1. The b-state mode n is b(n-1), and the c-state mode n is c(n+2). Finite tail intervals and genuine tensor induction supply all-state bilinearity.

Classical attribution: Bakalov-Kac, math/0402315v1 section 4.1; Matsuo-Nagatomo, hep-th/9706118v1. The imported coefficient kernels retain Scott Carnahan, vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache-2.0. Sugawara architecture retains Kalle Kytola, VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4, Apache-2.0. No literature novelty is asserted.

The field and current identities include degenerate lattices and rank zero. They impose no inverse-Gram or rank-26 hypothesis. The accepted total-charge square anomaly remains in LatticeBRSTSquare; pure ghost Qg is anomalous. The total-Q field derivation is proved in LatticeMatterGhostBRSTDerivation. This module does not prove coupled three-index Jacobi, no-ghost, full string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.conformal_modes`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.current_zero_mode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_locality`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_parity`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.stateField_vacuum_creation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField.tensor_coefficients`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState](../../Quantum/Fermionic/BcGhostConformalBRSTState.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateDerivative](../LatticeActualStateDerivative.md)
