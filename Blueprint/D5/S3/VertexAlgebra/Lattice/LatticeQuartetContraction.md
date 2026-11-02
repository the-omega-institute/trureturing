# LatticeQuartetContraction

## Abstract

LatticeQuartetContraction

Escape audit remains unfinished for the 39 public calculus and original-quartet targets: 37 compiled typed attempts are declared_unresolved (IE-C050 ClosedTruthReadout, reason=unclassified_form, rule=source.selection_missing; certificate null), and kernel_number_iff and literal_relative_ground have only full-telescope source bridges. No target is declared_validated. Exact source selection and whole-statement reconstruction remain missing; the two source-bridge-only targets also lack complete whole-family variation, slot sensitivity, actual observational dependence and Contract registration. The current-target limitation is linked at https://github.com/the-omega-institute/trureturing/issues/25604 under CLAUDE section 3.9. This issue supplies neither mathematical proof nor validated registration.

The actual tensor coordinate equivalence is constructed from the accepted all-charge polynomial equivalence and the identity on the original ghost Fock factor. The genuine basis retains every original integral charge, every longitudinal and transverse polynomial exponent at frequency r+1, and every finite ghost occupation set. totalCount is the unweighted number of longitudinal occupations plus the accepted ghost count, not the energy. invM is its reciprocal diagonal, zero at count zero; P0 is the full zero-count projector; h=R invM. The actual local number sum is proved to have this spectrum. The contraction is an all-state endomorphism equality and is not inferred from finite tests. Full P0 still permits ghost site 3: its ghost factors are ket{1} and ket{1,3}. Only the explicit actual ker(b0) restriction removes the latter. The later physical energy shell, full BRST remainder, HPL, no-ghost, positivity, mass-shell and AdS endpoints remain separate proof obligations. These concrete results are repository derivations reusing accepted coordinate and ghost-count suppliers, without literature novelty claims.

**Theorem 1.1 (M_basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.M_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.M_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine combined original tensor basis is diagonal for the actual locally finite M, with eigenvalue the sum of both longitudinal polynomial occupations and the accepted original ghost count. Source telescope (with the module variables described above): (i : StateIndex D t) : M F (actualBasis F B i) = (totalCount i : ℂ) • actualBasis F B i

**Theorem 1.2 (homotopy_contraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.homotopy_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.homotopy_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original lattice, null frame, actual finite transverse basis and original integral p with pPlus(p) nonzero, d0 h + h d0 = 1 - P0 as endomorphisms of the full original tensor carrier. Here h is defined to be R composed with the proved reciprocal actual count. Source telescope (with the module variables described above): (p : Charge D) (hp : F.pPlus p ≠ 0) : d0 F p * h F B p + h F B p * d0 F p = 1 - P0 F B

**Theorem 1.3 (homotopy_square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.homotopy_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.homotopy_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual inverse-count homotopy squares to zero for all original charges. Source telescope (with the module variables described above): (p : Charge D) : h F B p * h F B p = 0

**Theorem 1.4 (literal_relative_ground).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.literal_relative_ground`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.literal_relative_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a fixed original integral charge, the simultaneous conditions M v=0, actual b0 v=0 and charge projection v=v are equivalent to a transverse polynomial tensor the original c1-vacuum. This statement is only a literal algebraic kernel characterization; the physical relative BRST shell and remainder are not supplied. Source telescope (with the module variables described above): (p : Charge D) (v : State D) : (M F v = 0 ∧ ghostB0 v = 0 ∧ chargeProject p v = v) ↔ ∃ Q : MvPolynomial (Fin t × ℕ) ℂ, v = Finsupp.single p (transverseOriginal F B Q) ⊗ₜ[ℂ] D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac

**Theorem 1.5 (b0_d0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.b0_d0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.b0_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual ghost b0 anticommutes with the all-frequency d0. Source telescope (with the module variables described above): (p : Charge D) : ac (ghostB0 (D := D)) (d0 F p) = 0

**Theorem 1.6 (P0_commutes_b0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_commutes_b0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_commutes_b0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full zero-count projection commutes with the actual ghost b0. Source telescope (with the module variables described above): : P0 F B * ghostB0 = ghostB0 * P0 F B

**Theorem 1.7 (chargeProject_d0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.chargeProject_d0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.chargeProject_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original integral charge-sector projection commutes with d0. Source telescope (with the module variables described above): (p q : Charge D) : chargeProject p * d0 F q = d0 F q * chargeProject p

**Theorem 1.8 (chargeProject_R).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.chargeProject_R`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.chargeProject_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original integral charge-sector projection commutes with R. Source telescope (with the module variables described above): (p q : Charge D) : chargeProject p * R F q = R F q * chargeProject p

**Theorem 1.9 (h_mul_P0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.h_mul_P0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.h_mul_P0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual homotopy annihilates the full zero-count projector on its right. Source telescope (with the module variables described above): (p : Charge D) : h F B p * P0 F B = 0

**Theorem 1.10 (P0_mul_h).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_mul_h`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_mul_h` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full zero-count projector annihilates the actual homotopy on its right. Source telescope (with the module variables described above): (p : Charge D) : P0 F B * h F B p = 0

**Theorem 1.11 (d0_mul_P0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.d0_mul_P0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.d0_mul_P0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual d0 annihilates the full zero-count projector; proved from the original positive c modes and vanishing longitudinal derivatives at zero count. Source telescope (with the module variables described above): (p : Charge D) : d0 F p * P0 F B = 0

**Theorem 1.12 (P0_mul_d0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_mul_d0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_mul_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full zero-count projector annihilates d0 on its right. Source telescope (with the module variables described above): (p : Charge D) : P0 F B * d0 F p = 0

**Theorem 1.13 (b0_h).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.b0_h`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.b0_h` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual ghost b0 anticommutes with the actual inverse-count homotopy. Source telescope (with the module variables described above): (p : Charge D) : ac (ghostB0 (D := D)) (h F B p) = 0

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.M_basis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_commutes_b0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_mul_d0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.P0_mul_h`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.b0_d0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.b0_h`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.chargeProject_R`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.chargeProject_d0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.d0_mul_P0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.h_mul_P0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.homotopy_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.homotopy_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction.literal_relative_ground`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators](LatticeQuartetOperators.md)
