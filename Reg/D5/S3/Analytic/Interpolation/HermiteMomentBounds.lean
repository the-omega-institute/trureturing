import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.HermiteMomentBounds
import Reg.Support.DependentFamily

/-! Source-bound audit of the strict square-sum inequality for positive coordinates. -/

namespace Reg.D5.S3.Analytic.Interpolation.HermiteMomentBounds

open _root_.D5.S3.Analytic.Interpolation.HermiteMomentBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the square of the total coordinate sum in every dimension. -/
abbrev signature : Signature where
  Params := ℕ
  State k := Fin k → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => (∑ i, x i) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve the original implicit dimension, hypotheses, and strict inequality. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {k : ℕ}, 2 ≤ k → ∀ x : Fin k → ℝ, (∀ i, 0 < x i) →
    (∑ i, x i ^ 2) < r.readout () k x

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (k := 2) (by norm_num) (fun _ => 1) (fun _ => by norm_num)
  norm_num [rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena
    (∀ {k : ℕ}, 2 ≤ k → ∀ x : Fin k → ℝ, (∀ i, 0 < x i) →
      (∑ i, x i ^ 2) < (∑ i, x i) ^ 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_sq_lt_sq_sum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.Interpolation.HermiteMomentBounds.sum_sq_lt_sq_sum)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.HermiteMomentBounds.sum_sq_lt_sq_sum_unit
  realizationName :=
    `Reg.D5.S3.Analytic.Interpolation.HermiteMomentBounds.source_registration
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
    (realize signature (fun _ _ x => (∑ i, x i) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.HermiteMomentBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Analytic.Interpolation.HermiteMomentBounds.sum_sq_lt_sq_sum
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Analytic.Interpolation.HermiteMomentBounds
