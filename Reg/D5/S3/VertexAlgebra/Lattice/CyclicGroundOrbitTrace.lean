import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace

/-! Source registration for the actual finite-orbit ground trace. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Reg.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.Lattice
open _root_.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace
open _root_.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitBasis
open _root_.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace
open _root_.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
open _root_.D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient

abbrev Statement : Prop := type_of% (@corrected_ground_cycle_power_trace)

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => if s then Statement else False) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change False at h
  exact h

def family : Registration arena (type_of% (@corrected_ground_cycle_power_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨corrected_ground_cycle_power_trace, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨(), true, false, ?_⟩
    intro h
    have hf : False := Eq.mp h corrected_ground_cycle_power_trace
    exact hf

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@corrected_ground_cycle_power_trace)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace.family
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
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace
