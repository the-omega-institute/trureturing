# Ordinary Hermitian form on the original matter-ghost tensor states

## Abstract

Ordinary Hermitian form on the original matter-ghost tensor states

Let D : LatticeData. State D is the original algebraic tensor Carrier D tensor the original countable bc occupation Fock space. Hm and Hg are the existing ordinary Hermitian forms. All states, charges, ranks and integer modes retain their original ranges; finite supports belong to the individual algebraic states.

Source placement revision: the two original subtraction helper names Hmg_sub_left and Hmg_sub_right are absent from this first module and its Reg and declaration-description inventories. Their exact public statements and proofs are retained once in the saved future PhysicalPairing source, under their original qualified namespace, next to their original inserted_sub_left/right consumers. That later source is deferred and has not been applied or accepted.

**Definition 1.1 (The original tensor Hermitian form).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D and x,y : State D, Hmg x y is the double finite-support sum Hm v w * Hg (ket S) (ket T) over the actual ghost-basis slices of x and y.

**Theorem 1.2 (Zero in the first argument).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_zero_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_zero_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and y : State D, Hmg 0 y = 0.

**Theorem 1.3 (Zero in the second argument).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_zero_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_zero_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and x : State D, Hmg x 0 = 0.

**Theorem 1.4 (Additivity in the first argument).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_add_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_add_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and x,z,y : State D, Hmg (x+z) y = Hmg x y + Hmg z y.

**Theorem 1.5 (Conjugate linearity in the first argument).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_smul_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_smul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, a : Complex and x,y : State D, Hmg (a smul x) y = star a * Hmg x y.

**Theorem 1.6 (Ordinary Hermitian symmetry).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and x,y : State D, Hmg x y = star (Hmg y x).

**Theorem 1.7 (Additivity in the second argument).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_add_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_add_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and x,y,z : State D, Hmg x (y+z) = Hmg x y + Hmg x z.

**Theorem 1.8 (Linearity in the second argument).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_smul_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_smul_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, a : Complex and x,y : State D, Hmg x (a smul y) = a * Hmg x y.

**Theorem 1.9 (The original pure-tensor formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, v,w : Carrier D and u,z : the original Fock, Hmg (v tensor u) (w tensor z) = Hm v w * Hg u z.

**Theorem 1.10 (Adjoint of every b mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostB`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, m : Int and x,y : State D, Hmg (ghostB D m x) y = Hmg x (ghostB D (-m) y).

**Theorem 1.11 (Adjoint of every c mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostC`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, m : Int and x,y : State D, Hmg (ghostC D m x) y = Hmg x (ghostC D (-m) y).

**Theorem 1.12 (Adjoint of the actual lifted cubic charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostCharge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostCharge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and x,y : State D, Hmg (ghostCharge D x) y = Hmg x (ghostCharge D y), with ghostCharge the tensor lift of the actual cubic Qg.

**Theorem 1.13 (Adjoint of every matter mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_matterMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_matterMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and H : Matrix (Fin D.rank) (Fin D.rank) Complex satisfying H * gramComplex D = 1 and gramComplex D * H = 1, every m : Int and x,y : State D satisfy Hmg (matterMode D H m x) y = Hmg x (matterMode D H (-m) y).

**Theorem 1.14 (Adjoint of the locally finite coupling).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_T`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and H : Matrix (Fin D.rank) (Fin D.rank) Complex satisfying H * gramComplex D = 1 and gramComplex D * H = 1, every x,y : State D satisfy Hmg (T D H x) y = Hmg x (T D H y). The proof uses a common statewise finite capture closed under m maps to -m.

**Theorem 1.15 (Adjoint of the original total charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_totalCharge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_totalCharge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and H : Matrix (Fin D.rank) (Fin D.rank) Complex satisfying H * gramComplex D = 1 and gramComplex D * H = 1, every x,y : State D satisfy Hmg (totalCharge D H x) y = Hmg x (totalCharge D H y), with totalCharge D H = T D H + ghostCharge D.

The source retains the suppliers and attribution Bakalov--Kac, Scott Carnahan, Kalle Kytölä, Mathlib, Batteries, and the original BRST literature. This tensor extension reuses their existing factor-adjoint theorems. These descriptions identify the repository construction and do not assert literature priority.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_T`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_add_left`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_add_right`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostB`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostC`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_ghostCharge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_hermitian`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_matterMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_smul_left`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_smul_right`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_totalCharge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_zero_left`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostHermitian.Hmg_zero_right`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian](../../../Quantum/Fermionic/BcGhostBRSTHermitian.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](../LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian](../../SourceBPZ/OriginalMatterHermitian.md)
