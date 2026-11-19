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
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => decide (s = true)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ s : Bool,
    (r.readout () () s = true) ↔ (if s then Statement else False)

private theorem bridge :
    (type_of% (@corrected_ground_cycle_power_trace_observed)) ↔ arena.Law actual := by
  constructor
  · intro h s
    simpa [actual, realize] using h s
  · intro h s
    simpa [actual, realize] using h s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Statement := corrected_ground_cycle_power_trace
  have hf : False := by
    simpa [rejected, realize] using (h true).mpr hs
  exact hf

def family : Registration arena
    (type_of% (@corrected_ground_cycle_power_trace_observed)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp corrected_ground_cycle_power_trace_observed, rejected, rejected_law⟩
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
    simp [actual, realize]

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@corrected_ground_cycle_power_trace_observed)
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
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace
