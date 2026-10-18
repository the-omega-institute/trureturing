import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
open _root_.D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a m => ∑ j ∈ range a, sin (m * (π * j / a)) ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a m : ℕ}, 0 < a → sin (π * m / a) ≠ 0 →
    R.readout () a m = a / 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (a := 2) (m := 1) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, realize, sum_range_succ]

def source_registration : Registration arena (type_of% @sum_sin_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_sin_sq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sum_sin_sq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros.unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ a m => ∑ j ∈ range a, sin (m * (π * j / a)) ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
