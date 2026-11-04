import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.IndependenceComplexTorsionSeed
/-! A dependent source registration for the boundary-annihilating detector. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.IndependenceComplexTorsionSeed
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Geometry.IndependenceComplexTorsionSeed
abbrev signature : Signature where
  Params := Unit
  State _ := C2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := C1
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ c => d2 c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => Pi.single 7 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ c : C2, detector (R.readout () () c) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0
  change detector (Pi.single 7 1) = 0 at hbad
  have hvalue : detector (Pi.single 7 1) = 1 := by decide
  exact one_ne_zero (hvalue.symm.trans hbad)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, Pi.single 0 1, ?_⟩
  change d2 0 ≠ d2 (Pi.single 0 1)
  intro h
  have hentry := congrFun h 0
  have hne : d2 0 0 ≠ d2 (Pi.single 0 1) 0 := by decide
  exact hne hentry
def family : Registration arena (type_of% detector_d2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨detector_d2, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      have heq : other = role := by
        exact Subsingleton.elim (α := Unit) other role
      exact (hne heq).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence
def detectorBoundaryRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    detector_d2 (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.IndependenceComplexTorsionSeed.detector_d2.__information_unit
  realizationName := `Reg.D5.S3.Geometry.IndependenceComplexTorsionSeed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => d2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.IndependenceComplexTorsionSeed
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Geometry.IndependenceComplexTorsionSeed
