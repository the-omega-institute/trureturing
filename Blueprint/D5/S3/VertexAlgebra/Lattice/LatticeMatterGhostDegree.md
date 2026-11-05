# Ghost degrees on the original matter tensor carrier

## Abstract

Ghost degrees on the original matter tensor carrier

For every lattice datum D, the state space is Carrier D tensor the original complex bc occupation Fock space. H is an arbitrary complex matrix indexed by Fin D.rank; no inverse-Gram hypothesis is needed for these degree statements. The number operator acts only on the ghost factor.

**Definition 1.1 (The tensor number operator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData, tensorNumber D is BcGhostChargeTensor.number with matter module Carrier D, namely the identity on matter tensored with ghostNumber.

**Theorem 1.2 (The matter coupling has degree one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_T`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData and H : Matrix (Fin D.rank) (Fin D.rank) Complex, tensorNumber D * T D H - T D H * tensorNumber D = T D H. A common finite capture of x and tensorNumber D x permits the modewise ghost-number identity to be summed on every original tensor state.

**Definition 1.3 (The lifted cubic).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.G`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData, G D is the identity on Carrier D tensored with the original cubic Qg.

**Definition 1.4 (The total matter and cubic charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.Q`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData and complex rank-indexed matrix H, Q D H = T D H + G D.

**Definition 1.5 (The square comparison residual).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.E`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData and complex rank-indexed matrix H, E D H = (Q D H)^2 - ((26-rank(D))/26) smul (G D)^2, with scalars in Complex.

**Theorem 1.6 (The lifted cubic has degree one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_G`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_G` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData, tensorNumber D * G D - G D * tensorNumber D = G D. The pure ghost cubic degree identity is transported through the actual tensor map.

**Theorem 1.7 (The total charge has degree one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_Q`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData and complex rank-indexed matrix H, tensorNumber D * Q D H - Q D H * tensorNumber D = Q D H. Both summands are the original operators.

**Theorem 1.8 (The actual residual has degree two).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_E`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_E` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData and complex rank-indexed matrix H, tensorNumber D * E D H - E D H * tensorNumber D = (2 : Complex) smul E D H. The derivation identity for a square applied to the degree-one total and cubic charges proves this without assuming an anomaly formula or a commutant conclusion.

This algebraic result is a step toward the Monster, VOA/CFT, anomaly and fusion programme. BRST cohomology, the no-ghost theorem, a physical string model and an AdS/CFT correspondence require further constructions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.E`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.G`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.Q`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_E`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_G`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_Q`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree.tensorNumber_T`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostBRSTDegree](../../Quantum/Fermionic/BcGhostBRSTDegree.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostChargeTensor](../../Quantum/Fermionic/BcGhostChargeTensor.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling](LatticeMatterGhostCoupling.md)
