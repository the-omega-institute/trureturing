import D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The complete source telescope with one dependent readout and whole-family variation. -/

namespace Reg.D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues

open _root_.D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues
open _root_.D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev sig : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig := realize sig (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization sig := realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R :=
    (∀ k : ℤ, 1 ≤ k → (UniqueValue k ↔ ∃ t : ℕ, 1 ≤ t ∧ k = sequenceValue t)) ∧
    (∃ r : ℕ → ℕ, r = realizingOrder ∧ ∀ t : ℕ, 1 ≤ t →
      2 ≤ r t ∧ 1 ≤ sequenceValue (R.readout () () t) ∧
      ((jaco (r t)).maxDegree : ℤ) = sequenceValue t ∧
      ∀ m : ℕ, 1 ≤ m → ((jaco m).maxDegree : ℤ) = sequenceValue t → m = r t)

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨r, hr, hfamily⟩ := h.2
  have hp := (hfamily 1 (by decide)).2.1
  change 1 ≤ sequenceValue 0 at hp
  norm_num [sequenceValue] at hp

private theorem depends : ObservationalDependence sig actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; omega⟩

def evidence : Registration arena (type_of% @_root_.D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues.result, rejected, bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := depends

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues.result) (Realization sig) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues.result.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "arg", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

end
end Reg.D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues
