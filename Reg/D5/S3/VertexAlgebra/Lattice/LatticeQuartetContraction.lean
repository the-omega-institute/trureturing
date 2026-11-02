import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators

/-! Faithful full-telescope source-family attempts. Structural source recognition
is judged separately; compiled registrations do not imply declared_validated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeLightConeCoordinates LatticeQuartetContraction NullFrame
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open scoped BigOperators TensorProduct
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.Witness
namespace M_basis
abbrev signature : Signature where
  Params := LatticeData
  State p := State p × State p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (i : StateIndex D t),
    obs.readout () D (M F (actualBasis F B i),(totalCount i : ℂ) • actualBasis F B i)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_basis)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis (⟨0,0⟩,∅)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_basis)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_basis), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (State p)
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.M_basis) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.M_basis.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.M_basis.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end M_basis
namespace homotopy_contraction
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D) (hp : F.pPlus p ≠ 0),
    obs.readout () D (d0 F p * h F B p + h F B p * d0 F p,1 - P0 F B)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.homotopy_contraction)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis charge pPlus_ne
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.homotopy_contraction)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.homotopy_contraction), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.homotopy_contraction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.homotopy_contraction.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.homotopy_contraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end homotopy_contraction
namespace homotopy_square
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D),
    obs.readout () D (h F B p * h F B p,0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.homotopy_square)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.homotopy_square)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.homotopy_square), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.homotopy_square) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.homotopy_square.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.homotopy_square.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end homotopy_square
namespace literal_relative_ground
structure Params where
  D : LatticeData
  F : NullFrame D
  t : ℕ
  B : Module.Basis (Fin t) ℂ F.K
  p : Charge D
abbrev signature : Signature where
  Params := Params
  State p := State p.D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun role p x => if role then
    (∃ Q : MvPolynomial (Fin p.t × ℕ) ℂ,
      x = Finsupp.single p.p (transverseOriginal p.F p.B Q) ⊗ₜ[ℂ]
        _root_.D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac)
    else (M p.F x = 0 ∧ ghostB0 x = 0 ∧ chargeProject p.p x = x))
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D) (x : State D),
    obs.readout false ⟨D,F,t,B,p⟩ x ↔ obs.readout true ⟨D,F,t,B,p⟩ x
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.literal_relative_ground)) ↔ arena.Law actual := Iff.rfl
theorem source_actual : arena.Law actual := source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.literal_relative_ground)
-- Whole-family variation, slot sensitivity, actual observational dependence and
-- a recognized native source-selection certificate remain unfinished here.
end literal_relative_ground
namespace b0_d0
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p : Charge D),
    obs.readout () D (ac (ghostB0 (D := D)) (d0 F p),0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.b0_d0)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.b0_d0)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.b0_d0), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.b0_d0) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.b0_d0.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.b0_d0.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end b0_d0
namespace P0_commutes_b0
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) ,
    obs.readout () D (P0 F B * ghostB0,ghostB0 * P0 F B)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_commutes_b0)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_commutes_b0)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_commutes_b0), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_commutes_b0) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.P0_commutes_b0.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.P0_commutes_b0.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end P0_commutes_b0
namespace chargeProject_d0
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p q : Charge D),
    obs.readout () D (chargeProject p * d0 F q,d0 F q * chargeProject p)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject_d0)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject_d0)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject_d0), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject_d0) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.chargeProject_d0.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.chargeProject_d0.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end chargeProject_d0
namespace chargeProject_R
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) (p q : Charge D),
    obs.readout () D (chargeProject p * R F q,R F q * chargeProject p)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject_R)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject_R)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject_R), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.chargeProject_R) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.chargeProject_R.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.chargeProject_R.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end chargeProject_R
namespace h_mul_P0
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D),
    obs.readout () D (h F B p * P0 F B,0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.h_mul_P0)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.h_mul_P0)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.h_mul_P0), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.h_mul_P0) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.h_mul_P0.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.h_mul_P0.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end h_mul_P0
namespace P0_mul_h
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D),
    obs.readout () D (P0 F B * h F B p,0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_mul_h)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_mul_h)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_mul_h), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_mul_h) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.P0_mul_h.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.P0_mul_h.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end P0_mul_h
namespace d0_mul_P0
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D),
    obs.readout () D (d0 F p * P0 F B,0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_mul_P0)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_mul_P0)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_mul_P0), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.d0_mul_P0) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.d0_mul_P0.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.d0_mul_P0.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end d0_mul_P0
namespace P0_mul_d0
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D),
    obs.readout () D (P0 F B * d0 F p,0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_mul_d0)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_mul_d0)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_mul_d0), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.P0_mul_d0) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.P0_mul_d0.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.P0_mul_d0.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end P0_mul_d0
namespace b0_h
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p) × Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ x => x.1 = x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D),
    obs.readout () D (ac (ghostB0 (D := D)) (h F B p),0)
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.b0_h)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h frame basis 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetContraction.b0_h)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetContraction.b0_h), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne; exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : LatticeData := zeroLattice
    obtain ⟨z,w,hw⟩ := exists_pair_ne (Module.End ℂ (State p))
    refine ⟨p, (z,z), (z,w), ?_⟩
    intro he; exact hw (Eq.mp he rfl)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetContraction.b0_h) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.b0_h.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction.b0_h.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Paired actual operands reconstruct the full source through source_bridge.
  -- No native source-selection certificate for this encoding has been established.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end b0_h
end Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
