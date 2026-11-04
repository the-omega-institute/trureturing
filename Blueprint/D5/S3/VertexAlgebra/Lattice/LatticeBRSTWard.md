# Ward identities of the original total BRST charge

## Abstract

Ward identities of the original total BRST charge

Let D : LatticeData and H : Matrix (Fin D.rank) (Fin D.rank) Complex. All operators act on State D = Carrier D tensor the original countable bc occupation Fock space. B_r, C_r, M_r and V_r denote ghostB D r, ghostC D r, matterMode D H r and ghostVirasoro D r. Brackets below are ordinary commutators and braces are anticommutators. Every mode index ranges over all integers.

**Definition 1.1 (The lifted original cubic).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostCharge`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D, ghostCharge D = TensorProduct.map LinearMap.id BcGhostBRST.Qg.

**Definition 1.2 (The total original charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.totalCharge`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.totalCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,H, totalCharge D H = T D H + ghostCharge D. No c-zero or intercept term is added.

**Definition 1.3 (The lifted c Ward operator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostR`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D and r : Int, ghostR D r is the identity on matter tensored with BcGhostBRST.R r.

**Definition 1.4 (The native ghost anomaly on the tensor carrier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D, ghostSquareAnomaly D is the identity on matter tensored with BcGhostBRST.squareAnomaly, the statewise finite signed sum with coefficient (-26/24)(n^3-n).

**Theorem 1.5 (The b Ward identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_ward_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_ward_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H and r : Int, {totalCharge D H, B_r} = M_r + V_r. No inverse-Gram hypothesis is required.

**Theorem 1.6 (The c Ward identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_ward_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_ward_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H and r : Int, {totalCharge D H, C_r} = ghostR D r. No inverse-Gram hypothesis is required.

**Theorem 1.7 (Identification of the native ghost square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostCharge_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostCharge_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, ghostCharge D * ghostCharge D = ghostSquareAnomaly D. This uses the full native ghost square theorem on the original Fock representation.

**Theorem 1.8 (The ghost anomaly b commutator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and r : Int, [ghostSquareAnomaly D, B_r] = BcGhostBRST.anomalyCoefficient r smul C_r. The coefficient is (26/12)(r^3-r).

**Theorem 1.9 (The ghost anomaly c commutator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and r : Int, [ghostSquareAnomaly D, C_r] = 0.

**Theorem 1.10 (The finite matter and R commutator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.T_R`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.T_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H and r : Int, [T D H, ghostR D r] = 0. The pure-c CAR gives the modewise relation. One finite capture of x and ghostR D r x extends it to every algebraic tensor state; no operator-family support or matter-vacuum condition is used.

**Theorem 1.11 (Commutation with the c Ward operator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_R`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H and r : Int, [totalCharge D H, ghostR D r] = 0.

**Theorem 1.12 (The exact rank-dependent covariance).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H satisfying H * gramComplex D = 1 and gramComplex D * H = 1, and every r : Int, [totalCharge D H, M_r + V_r] = ((26-rank(D))/12)(r^3-r) smul C_r. The matter contribution is minus rank(D)/12 and the cubic ghost contribution is plus 26/12.

**Theorem 1.13 (The total square b commutator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_square_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_square_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H satisfying the two inverse-Gram identities and every r : Int, [(totalCharge D H)*(totalCharge D H), B_r] = ((26-rank(D))/12)(r^3-r) smul C_r. Associativity identifies this with [Q,{Q,B_r}], with no factor of one half.

**Theorem 1.14 (The total square c commutator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_square_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_square_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H and every r : Int, [(totalCharge D H)*(totalCharge D H), C_r] = 0. No inverse-Gram hypothesis is required.

**Definition 1.15 (The scaled square residual).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,H, squareResidual D H = totalCharge D H * totalCharge D H - ((26-rank(D))/26) smul ghostSquareAnomaly D.

**Theorem 1.16 (Commutation of the residual with every b mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H satisfying the two inverse-Gram identities and every r : Int, squareResidual D H * B_r = B_r * squareResidual D H. The native ghost anomaly coefficient cancels the total square coefficient exactly.

**Theorem 1.17 (Commutation of the residual with every c mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H and every r : Int, squareResidual D H * C_r = C_r * squareResidual D H.

This algebraic result is a step toward the Monster, VOA/CFT, anomaly and fusion programme. BRST cohomology, the no-ghost theorem, a physical string model and an AdS/CFT correspondence require further constructions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.T_R`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostCharge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostCharge_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostR`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly_b`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.ghostSquareAnomaly_c`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual_b`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.squareResidual_c`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.totalCharge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_R`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_square_b`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_square_c`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_ward_b`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard.total_ward_c`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostChargeTensor](../../Quantum/Fermionic/BcGhostChargeTensor.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostSquare](../../Quantum/Fermionic/BcGhostSquare.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCovariance](LatticeMatterGhostCovariance.md)
