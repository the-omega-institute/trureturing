import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Analytic.Chebyshev.PositivityThreshold

/-! Source-bound registrations for the positivity threshold of Chebyshev values. The
criterion record selects the value `T_n(s)`, read out as a function of the index `n` at a
fixed point `s`. The first-sign-change record selects `cos (n α)`, read out as a function of
`n` at a fixed angle `α`. Every other clause is kept verbatim. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Chebyshev.PositivityThreshold
open Polynomial Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Analytic.Chebyshev.PositivityThreshold

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)

namespace Criterion

def actual : Realization signature :=
  realize signature (fun _ s n => (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval s)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : ℝ, (∀ n : ℕ, 1 ≤ n → 0 < R.readout () s n) ↔ 1 ≤ s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0).mp (fun _ _ => by simp [rejected, realize])
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  simp [actual, realize]

def source : Registration arena (type_of% @forall_pos_eval_T_iff_one_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@forall_pos_eval_T_iff_one_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@forall_pos_eval_T_iff_one_le) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Chebyshev.PositivityThreshold.Criterion.unit
  realizationName := `Reg.D5.S3.Analytic.Chebyshev.PositivityThreshold.Criterion.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ s n => (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Chebyshev.PositivityThreshold
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Criterion

namespace FirstSignChange

def actual : Realization signature :=
  realize signature (fun _ α n => Real.cos ((n : ℝ) * α)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : ℝ} (_ : 0 < α) (_ : α < π),
    Real.cos (((⌊π / (2 * α)⌋₊ + 1 : ℕ) : ℝ) * α) < 0 ∧
      ∀ n : ℕ, n < ⌊π / (2 * α)⌋₊ + 1 → 0 ≤ R.readout () α n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (α := π / 2) (by positivity) (by linarith [Real.pi_pos])).2 0
    (Nat.succ_pos _)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨π, 0, 1, ?_⟩
  norm_num [actual, realize]

def source : Registration arena
    (type_of% @cos_floor_succ_mul_neg_and_cos_nonneg_before) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cos_floor_succ_mul_neg_and_cos_nonneg_before, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cos_floor_succ_mul_neg_and_cos_nonneg_before) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Chebyshev.PositivityThreshold.FirstSignChange.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Chebyshev.PositivityThreshold.FirstSignChange.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ α n => Real.cos ((n : ℝ) * α))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Chebyshev.PositivityThreshold
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end FirstSignChange

end Reg.D5.S3.Analytic.Chebyshev.PositivityThreshold
