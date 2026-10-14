# The actual tensor form and relative antighost kernel

## Abstract

Relative preimages annihilate both native inserted-C0 boundary obstructions.

On the unrestricted algebraic matter tensor ghost State D, F is the actual matter hermitianForm times the energy-rotated Hplus on pure tensors. The physical C0 is C D 0, namely the tensor lift of c(0), or ghost currentMode .c (-2). Pi is the native tensor parity operator. Q is the original finite-support BRST charge. Both inverse-Gram equations are retained whenever its form adjoint is used.

**Theorem 1.1 (Actual antighost form transpose).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.F_B`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.F_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

F(B(mode) left,right)=F(Pi left,B(-mode) right) on every tensor state, by the original matter tensor form and the rotated ghost antighost transpose.

**Theorem 1.2 (The relative kernel is isotropic for F).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.relative_isotropic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.relative_isotropic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If B0 kills both inputs, their uninserted F pairing is zero. The actual CAR gives left=B0(C0 left); the proved B0 transpose then places B0 on the right input. This is isotropy of the uninserted form, not degeneracy or positivity of the C0-inserted physical form.

**Theorem 1.3 (Parity preserves the relative kernel).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.Pi_relative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.Pi_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pi anticommutes with B0, so a relative vector remains relative after applying Pi.

**Theorem 1.4 (The actual obstruction operator preserves relativity).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.V0_relative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.V0_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

V0 is the original statewise finite sum of 2n times C(-n)C(n). At n=0 its coefficient vanishes. At every nonzero n the CAR anticommutes B0 through both C factors; each weighted summand preserves ker B0, and so does their actual finsum. No universal vanishing of V0 is asserted.

**Theorem 1.5 (Left boundary obstruction with its positive sign).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.left_boundary_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.left_boundary_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Q-cycle y and arbitrary ambient u, F(Q u,C0 y)=one-half F(Pi u,V0 y). The sign is positive: the negative original-Q transpose combines with the negative actual anticommutator {Q,C0}=-V0/2.

**Theorem 1.6 (Right boundary obstruction with its negative sign).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.right_boundary_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.right_boundary_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Q-cycle x and arbitrary ambient u, F(x,C0 Q u)=-one-half F(x,V0 u). The other term is F(x,Q C0 u), which vanishes by the actual cycle-boundary orthogonality with an unrestricted ambient preimage.

**Theorem 1.7 (Both inserted boundary pairings vanish for relative preimages).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.boundary_pairing_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.boundary_pairing_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If u is relative and y is a relative Q-cycle, F(Q u,C0 y)=0 and F(y,C0 Q u)=0 simultaneously. Pi u, V0 y and V0 u are relative by the preceding actual operator laws, so uninserted relative isotropy kills both obstruction pairings. The preimage must be relative: these identities do not establish C0 descent on the entire original absolute cohomology.

## References

- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.F_B`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.Pi_relative`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.V0_relative`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.boundary_pairing_vanishes`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.left_boundary_obstruction`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.relative_isotropic`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm.right_boundary_obstruction`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostHermitianCohomology](../LatticeBcGhostHermitianCohomology.md)
- Dependency: [D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint](RotatedAntighostAdjoint.md)
