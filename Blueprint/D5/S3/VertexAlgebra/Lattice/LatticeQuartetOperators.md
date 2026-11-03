# LatticeQuartetOperators

## Abstract

LatticeQuartetOperators

Escape audit remains unfinished for the 39 public calculus and original-quartet targets: 37 compiled typed attempts are declared_unresolved (IE-C050 ClosedTruthReadout, reason=unclassified_form, rule=source.selection_missing; certificate null), and kernel_number_iff and literal_relative_ground have only full-telescope source bridges. No target is declared_validated. Exact source selection and whole-statement reconstruction remain missing; the two source-bridge-only targets also lack complete whole-family variation, slot sensitivity, actual observational dependence and Contract registration. The current-target limitation is linked at https://github.com/the-omega-institute/trureturing/issues/25604 under CLAUDE section 3.9. This issue supplies neither mathematical proof nor validated registration.

The carrier is exactly the original all-integral-charge lattice Carrier D tensor the original CountableOccupationFock.Fock. The operators a, b and c are the accepted original modes, with the original ghost cuts and signs. For k=r+1, dTerm pairs a(eMinus,k)c(-k) with a(eMinus,-k)c(k); rTerm pairs a(ePlus,-k)b(k) with a(ePlus,k)b(-k), both weighted by inverse k. Actual polynomial and ghost capture bounds prove local finiteness. d0=pPlus(p) times the unscaled sum, R=inverse pPlus(p) times its paired reciprocal-frequency sum, and M is the actual local number sum. No new mode relation, support, contraction or commutation premise is introduced. Original-current context is Bakalov and Kac, arXiv math/0402315v1, section 4.1. The concrete repository derivation reuses accepted LatticeLightConeCoordinates and BcGhostQuartetCount; no literature novelty is asserted.

**Theorem 1.1 (tp_tmul).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.tp_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.tp_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual tensor product of the two linear maps acts factorwise on original pure tensors. Source telescope (with the module variables described above): (A : Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock) (v : Carrier D) (w : Fock) : tp A G (v ⊗ₜ w) = A v ⊗ₜ G w

**Theorem 1.2 (tp_ac).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.tp_ac`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.tp_ac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tensor anticommutator splits into the actual matter commutator and ghost anticommutator contributions. Source telescope (with the module variables described above): (A B : Module.End ℂ (Carrier D)) (G H : Module.End ℂ Fock) : ac (tp A G) (tp B H) = tp (A * B - B * A) (G * H) + tp (B * A) (G * H + H * G)

**Theorem 1.3 (unscaled_contraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.unscaled_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.unscaled_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The locally finite sums of the actual unscaled original quartet modes have anticommutator equal to the locally finite actual number operator. Source telescope (with the module variables described above): : ac (unscaledD F) (unscaledR F) = M F

**Theorem 1.4 (original_contraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.original_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.original_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an original integral charge p with pPlus(p) nonzero, the actual scaled d0 and R have anticommutator M. This derives the count identity from the original mode relations. Source telescope (with the module variables described above): (p : Charge D) (hp : F.pPlus p ≠ 0) : d0 F p * R F p + R F p * d0 F p = M F

**Theorem 1.5 (d0_square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.d0_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.d0_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual all-frequency d0 squares to zero, without a nonzero pPlus assumption. Source telescope (with the module variables described above): (p : Charge D) : d0 F p * d0 F p = 0

**Theorem 1.6 (R_square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.R_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.R_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual all-frequency R squares to zero, including the totalized inverse convention at pPlus zero. Source telescope (with the module variables described above): (p : Charge D) : R F p * R F p = 0

**Theorem 1.7 (M_commutes_d0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.M_commutes_d0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.M_commutes_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual number operator commutes with d0, derived from the anticommutator and square-zero identities. Source telescope (with the module variables described above): (p : Charge D) : M F * d0 F p = d0 F p * M F

**Theorem 1.8 (M_commutes_R).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.M_commutes_R`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.M_commutes_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual number operator commutes with R, derived from the unscaled original identities. Source telescope (with the module variables described above): (p : Charge D) : M F * R F p = R F p * M F

**Theorem 1.9 (signed_support).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.signed_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.signed_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state, both the nonzero-integer d0 mode action and the reciprocal-natAbs-weighted R action have finite support. No support premise is added to the state. Source telescope (with the module variables described above): (v : State D) : (Function.support (fun n : ℤ => if n=0 then 0 else dm F n v)).Finite ∧ (Function.support (fun n : ℤ => if n=0 then 0 else ((n.natAbs : ℂ)⁻¹) • rr F n v)).Finite

**Theorem 1.10 (d0_signed_formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.d0_signed_formula`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.d0_signed_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed d0 equals pPlus(p) times the sum of all nonzero original integer modes a(eMinus,n) tensor c(-n), on every original state. Source telescope (with the module variables described above): (p : Charge D) (v : State D) : d0 F p v = F.pPlus p • ∑ᶠ n : ℤ, if n=0 then 0 else tp (a F.eMinus n) (c (-n)) v

**Theorem 1.11 (R_signed_formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.R_signed_formula`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.R_signed_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed R equals inverse pPlus(p) times the nonzero-integer sum of a(ePlus,-n) tensor b(n), weighted by inverse natAbs(n) at both signs. Source telescope (with the module variables described above): (p : Charge D) (v : State D) : R F p v = (F.pPlus p)⁻¹ • ∑ᶠ n : ℤ, if n=0 then 0 else ((n.natAbs : ℂ)⁻¹) • tp (a F.ePlus (-n)) (b n) v

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.M_commutes_R`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.M_commutes_d0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.R_signed_formula`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.R_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.d0_signed_formula`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.d0_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.original_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.signed_support`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.tp_ac`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.tp_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators.unscaled_contraction`
- Dependency: [D5/S3/HomologicalAlgebra/FiniteSupportEndomorphismCalculus](../../HomologicalAlgebra/FiniteSupportEndomorphismCalculus.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostQuartetCount](../../Quantum/Fermionic/BcGhostQuartetCount.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates](LatticeLightConeCoordinates.md)
