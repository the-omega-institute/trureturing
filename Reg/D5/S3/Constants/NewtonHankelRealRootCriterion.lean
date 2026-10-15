import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Constants.NewtonHankelRealRootCriterion
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Constants.NewtonHankelRealRootCriterion
open _root_.D5.S3.Constants.NewtonHankelRealRootCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe polynomial evaluation at the nonnegative argument. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ[X] (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ P x => P.eval x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P : ℝ[X]} {d : ℕ}
    (_hP : HasPositiveCoefficientsOfDegree P d) {x : ℝ} (_hx : 0 ≤ x),
      0 < R.readout () P x

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hP : HasPositiveCoefficientsOfDegree (C (1 : ℝ)) 0 := by
    constructor
    · simp
    · intro k hk
      have hkzero : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  have hbad := h hP (x := 0) le_rfl
  exact (lt_irrefl (0 : ℝ)) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨X, 0, 1, ?_⟩
  change (X : ℝ[X]).eval 0 ≠ (X : ℝ[X]).eval 1
  simp

def source_registration :
    Registration arena (type_of% @eval_pos_of_positive_coefficients) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eval_pos_of_positive_coefficients, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@eval_pos_of_positive_coefficients) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Constants.NewtonHankelRealRootCriterion.unit
  realizationName := `Reg.D5.S3.Constants.NewtonHankelRealRootCriterion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ P x => P.eval x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Constants.NewtonHankelRealRootCriterion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Constants.NewtonHankelRealRootCriterion
