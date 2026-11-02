import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeQuartetEnergyPreservation
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators

/-! Full-telescope source-family attempts. Exact source selection and binding
validation remain separate from the compiled mathematical preservation laws. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeLightConeCoordinates LatticeQuartetContraction
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetEnergyPreservation
open Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators.Witness

abbrev signature : Signature where
  Params := LatticeData
  State D := (State D × State D) × (State D × State D) × (State D × State D)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ x => x.1.1 = x.1.2 ∧ x.2.1.1 = x.2.1.2 ∧ x.2.2.1 = x.2.2.2)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

private theorem inverse_hyperbolic :
    gramComplex hyperbolic * gramComplex hyperbolic = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramComplex, hyperbolic, Matrix.mul_apply, Fin.sum_univ_two]

private theorem actual_dependence (role : Unit) :
    ∃ (D : LatticeData) (x y : signature.State D),
      actual.readout role D x ≠ actual.readout role D y := by
  have := state_nontrivial zeroLattice
  obtain ⟨z,w,hw⟩ := exists_pair_ne (State zeroLattice)
  refine ⟨zeroLattice, ((z,z),(z,z),(z,z)), ((z,w),(z,z),(z,z)), ?_⟩
  intro he
  exact hw ((Eq.mp he ⟨rfl,rfl,rfl⟩).1)

namespace d0_preserves_original_relative_constraints
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) 
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p q : Charge D) (x : State D)
    (hxCharge : chargeProject p x = x) (hxB0 : ghostB0 (D := D) x = 0)
    (hxEnergy : (LatticeMatterGhostCoupling.matterMode D H 0 +
      LatticeMatterGhostCoupling.ghostVirasoro D 0) x = 0),
    obs.readout () D
      ((chargeProject p (d0 F q x), d0 F q x),
       (ghostB0 (D := D) (d0 F q x), 0),
       ((LatticeMatterGhostCoupling.matterMode D H 0 +
         LatticeMatterGhostCoupling.ghostVirasoro D 0) (d0 F q x), 0))

theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh frame (gramComplex hyperbolic) inverse_hyperbolic inverse_hyperbolic 0 0 0 (by simp) (by simp) (by simp)

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetEnergyPreservation.d0_preserves_original_relative_constraints.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end d0_preserves_original_relative_constraints

namespace h_preserves_original_relative_constraints
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p q : Charge D) (x : State D)
    (hxCharge : chargeProject p x = x) (hxB0 : ghostB0 (D := D) x = 0)
    (hxEnergy : (LatticeMatterGhostCoupling.matterMode D H 0 +
      LatticeMatterGhostCoupling.ghostVirasoro D 0) x = 0),
    obs.readout () D
      ((chargeProject p (h F B q x), h F B q x),
       (ghostB0 (D := D) (h F B q x), 0),
       ((LatticeMatterGhostCoupling.matterMode D H 0 +
         LatticeMatterGhostCoupling.ghostVirasoro D 0) (h F B q x), 0))

theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh frame basis (gramComplex hyperbolic) inverse_hyperbolic inverse_hyperbolic 0 0 0 (by simp) (by simp) (by simp)

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetEnergyPreservation.h_preserves_original_relative_constraints.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end h_preserves_original_relative_constraints
end Reg.D5.S3.VertexAlgebra.Lattice.LatticeQuartetEnergyPreservation
