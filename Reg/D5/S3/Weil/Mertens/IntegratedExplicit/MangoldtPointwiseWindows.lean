import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass firstLiMass_lt_third)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

/-- The selected observable is the finite Mangoldt primitive at the argument in the window. -/
def actual : Realization signature :=
  realize signature (fun _ _ x => U x) (fun e => nomatch e)

private def changed : Realization signature := by
  classical
  exact realize signature (fun _ _ x => if RiemannHypothesis then x ^ 2 + 1 else 0)
    (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change U 0 ≠ U 1
  simp [U, Chebyshev.psi_zero, Chebyshev.psi_one]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

private theorem left_endpoint {Y : ℝ} (hY : 2 ≤ Y) : Y ∈ Icc Y (Y ^ (2 : ℝ)) := by
  rw [Real.rpow_two]
  exact ⟨le_rfl, by nlinarith⟩

namespace Power

def arena : Arena where
  signature := signature
  Law V := ∀ {b : ℝ}, 1 < b → (RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ →
    ∃ᶠ Y : ℝ in atTop, ∀ x ∈ Icc Y (Y ^ b), V.readout () () x ≤ x ^ ((1 : ℝ) / 2 + κ))

private theorem changed_fails : ¬ arena.Law changed := by
  classical
  intro H
  have h := H (b := 2) (by norm_num)
  by_cases hr : RiemannHypothesis
  · have hf := h.mp hr (1 / 2) (by norm_num)
    obtain ⟨Y, hw, hY⟩ := (hf.and_eventually (eventually_ge_atTop (2 : ℝ))).exists
    have hy := hw Y (left_endpoint hY)
    change (if RiemannHypothesis then Y ^ 2 + 1 else 0) ≤ Y ^ ((1 : ℝ) / 2 + 1 / 2) at hy
    simp only [hr, ↓reduceIte, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one] at hy
    nlinarith only [hy, hY]
  · apply hr
    apply h.mpr
    intro κ _
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    intro x hx
    change (if RiemannHypothesis then x ^ 2 + 1 else 0) ≤ _
    simpa only [hr, ↓reduceIte] using Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans (hY.trans hx.1)) _

def evidence : Registration arena (type_of% @rh_iff_pointwise_power_windows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rh_iff_pointwise_power_windows, changed, changed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_fails
  dependence := actual_dependence

end Power

namespace Sqrt

def arena : Arena where
  signature := signature
  Law V := ∀ {C b : ℝ}, firstLiMass < C → 1 < b → (RiemannHypothesis ↔
    ∀ R : ℝ, ∃ Y ≥ max R 2, ∀ x ∈ Icc Y (Y ^ b), V.readout () () x ≤ C * Real.sqrt x)

private theorem changed_fails : ¬ arena.Law changed := by
  classical
  intro H
  have h := H (C := 1) (b := 2) (firstLiMass_lt_third.trans (by norm_num)) (by norm_num)
  by_cases hr : RiemannHypothesis
  · obtain ⟨Y, hY, hw⟩ := h.mp hr 2
    have hY2 := (le_max_right _ _).trans hY
    have hy := hw Y (left_endpoint hY2)
    change (if RiemannHypothesis then Y ^ 2 + 1 else 0) ≤ 1 * Real.sqrt Y at hy
    simp only [hr, ↓reduceIte, one_mul] at hy
    have hs := Real.sqrt_le_self_iff.mpr (Or.inr (show 1 ≤ Y by linarith))
    nlinarith only [hy, hs, hY2]
  · apply hr
    apply h.mpr
    intro R
    refine ⟨max R 2, le_rfl, ?_⟩
    intro x _
    change (if RiemannHypothesis then x ^ 2 + 1 else 0) ≤ 1 * Real.sqrt x
    simpa only [hr, ↓reduceIte, one_mul] using Real.sqrt_nonneg x

def evidence : Registration arena (type_of% @rh_iff_pointwise_sqrt_windows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rh_iff_pointwise_sqrt_windows, changed, changed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_fails
  dependence := actual_dependence

end Sqrt

namespace Power

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rh_iff_pointwise_power_windows) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows.rh_iff_pointwise_power_windows
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows.Power.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => U x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "fn", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Power

namespace Sqrt

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rh_iff_pointwise_sqrt_windows) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows.rh_iff_pointwise_sqrt_windows
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows.Sqrt.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => U x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Sqrt

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
