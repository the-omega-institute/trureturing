import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Entire.DirectionalExponentialType
import Reg.Support.SingleDependentReadout

/-! The directional bound depends on the imaginary coordinate through its absolute value. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.Reg.Support
open _root_.D5.S3.Analytic.Entire
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Analytic.Entire.DirectionalExponentialType

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => |z.im|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F : ℂ → ℂ} (_hF : Differentiable ℂ F)
    {a B C : ℝ} {m : ℕ} (_ha : 0 ≤ a)
    (_hreal : ∀ x : ℝ, ‖F (x : ℂ)‖ ≤ B)
    (_hradial : ∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m * Real.exp (a * ‖z‖)),
    ∀ z : ℂ, ‖F z‖ ≤ max B C * (1 + ‖z‖) ^ m * Real.exp (a * R.readout () () z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hradial (z : ℂ) :
      ‖(1 : ℂ)‖ ≤ 1 * (1 + ‖z‖) ^ (0 : ℕ) * Real.exp (1 * ‖z‖) := by
    simpa using Real.one_le_exp (norm_nonneg z)
  have he := h (differentiable_const (1 : ℂ)) (a := 1) (B := 1) (C := 1) (m := 0)
    (by norm_num) (by simp) hradial 0
  change ‖(1 : ℂ)‖ ≤ max (1 : ℝ) 1 * (1 + ‖(0 : ℂ)‖) ^ (0 : ℕ) *
    Real.exp (1 * (-1)) at he
  have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  exact (not_le_of_gt hlt) (by simpa using he)

def family : Registration arena (type_of% @norm_le_exp_abs_im) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_le_exp_abs_im, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨(), (0 : ℂ), Complex.I, by change |(0 : ℂ).im| ≠ |Complex.I.im|; simp⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@norm_le_exp_abs_im) (Realization signature) Type Unit where
  unitName := `D5.S3.Analytic.Entire.norm_le_exp_abs_im.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Entire.DirectionalExponentialType.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => |z.im|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Entire.DirectionalExponentialType
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Entire.DirectionalExponentialType
