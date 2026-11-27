import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap
import Reg.Support.SingleDependentReadout

/-! Vary the actual arithmetic readout in the Fejér gap criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass)
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => U x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    V.readout () () x ≤ firstLiMass * Real.sqrt x - (Real.log x)^2/48 +
      Real.log x * Real.log (Real.log x)/12 + C*Real.log x

private def changed : Realization signature := by
  classical
  exact realize signature (fun _ _ x =>
    firstLiMass * Real.sqrt x - (Real.log x)^2/48 + Real.log x * Real.log (Real.log x)/12 +
      (if RiemannHypothesis then (Real.log x)^2 else 0)) (fun e => nomatch e)

private theorem changed_fails : ¬ arena.Law changed := by
  classical
  intro h
  by_cases hr : RiemannHypothesis
  · obtain ⟨C, hC, bound⟩ := h.mp hr
    obtain ⟨x, hx, hlog⟩ := (bound.and (Real.tendsto_log_atTop.eventually_gt_atTop (C+1))).exists
    change _ + (if RiemannHypothesis then (Real.log x)^2 else 0) ≤ _ at hx
    simp only [hr, ↓reduceIte] at hx
    nlinarith [mul_pos (show 0 < Real.log x by linarith) (show 0 < Real.log x-C by linarith)]
  · apply hr
    refine h.mpr ⟨0, le_rfl, ?_⟩
    filter_upwards with x
    change _ + (if RiemannHypothesis then (Real.log x)^2 else 0) ≤ _
    simp [hr]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change U 0 ≠ U 1
  have hIoc : Finset.Ioc (0 : ℕ) 1 = {1} := Nat.Ioc_succ_singleton 0
  norm_num [U, Chebyshev.psi_zero, Chebyshev.psi_one, hIoc,
    ArithmeticFunction.vonMangoldt_apply_one]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

def evidence : Registration arena (type_of% @rh_iff_eventually_uniform_fejer_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rh_iff_eventually_uniform_fejer_gap, changed, changed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_eventually_uniform_fejer_gap) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap.rh_iff_eventually_uniform_fejer_gap
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap.evidence
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
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap
