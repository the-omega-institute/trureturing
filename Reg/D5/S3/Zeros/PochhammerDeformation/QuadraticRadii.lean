import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.PochhammerDeformation.QuadraticRadii
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Zeros.PochhammerDeformation.QuadraticRadii
open _root_.D5.S3.Zeros.PochhammerDeformation.QuadraticRadii
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the second root in its linear factor. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the coefficient telescope, complete root multiset and factorization. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B c : ℂ), A ≠ 0 → ∃ z w : ℂ,
    (C A * X ^ 2 + C B * X + C c : ℂ[X]).roots = {z, w} ∧
    (C A * X ^ 2 + C B * X + C c : ℂ[X]) =
      C A * ((X - C z) * (X - C (R.readout () () w)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  obtain ⟨z, w, _, hf⟩ := bad 1 0 1 (by norm_num)
  have he := congrArg (fun p : ℂ[X] => p.eval 0) hf
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, zero_ne_one⟩

def source_registration : Registration arena (type_of% @quadratic_factors) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨quadratic_factors, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.PochhammerDeformation.QuadraticRadii.quadratic_factors)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.PochhammerDeformation.QuadraticRadii.unit
  realizationName := `Reg.D5.S3.Zeros.PochhammerDeformation.QuadraticRadii.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.PochhammerDeformation.QuadraticRadii
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Zeros.PochhammerDeformation.QuadraticRadii
