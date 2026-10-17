import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
import Reg.Support.DependentFamily

/-! Source-bound audit of the polynomial root defining the sharp three-coherence threshold. -/

namespace Reg.D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
open _root_.D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Evaluate the threshold polynomial at the candidate algebraic root. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ α => thresholdP α) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain the root interval, polynomial equation, and sharp attained upper bound. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∃ α : ℝ,
    6169 / 5000 < α ∧ α < 12339 / 10000 ∧ R.readout () () α = 0 ∧
    IsGreatest admissibleValues (thresholdN α / thresholdD α)

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨α, _, _, hzero, _⟩
  change (1 : ℝ) = 0 at hzero
  exact one_ne_zero hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change thresholdP 0 ≠ thresholdP 1
  norm_num [thresholdP]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ α => thresholdP α) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
    definition := some {
      owner := `D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
      name := `D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
