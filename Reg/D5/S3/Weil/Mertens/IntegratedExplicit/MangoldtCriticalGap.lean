import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
import Reg.Support.SingleDependentReadout

/-! Vary the original Mangoldt remainder in the exact biconditional. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass)
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => U x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := RiemannHypothesis ↔
    Tendsto (fun x : ℝ => firstLiMass * Real.sqrt x - V.readout () () x) atTop atTop

private def changed : Realization signature := by
  classical
  exact realize signature (fun _ _ x =>
    if RiemannHypothesis then firstLiMass * Real.sqrt x else firstLiMass * Real.sqrt x - x)
    (fun e => nomatch e)

private theorem changed_fails : ¬ arena.Law changed := by
  classical
  intro h
  by_cases hr : RiemannHypothesis
  · have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := by
      simpa only [changed, realize, hr, ↓reduceIte, sub_self] using h.mp hr
    obtain ⟨a, ha⟩ := eventually_atTop.mp (hzero.eventually_ge_atTop (1 : ℝ))
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (ha a le_rfl)
  · apply hr
    apply h.mpr
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [eventually_ge_atTop B] with x hx
    change B ≤ firstLiMass * Real.sqrt x -
      (if RiemannHypothesis then firstLiMass * Real.sqrt x else firstLiMass * Real.sqrt x - x)
    rw [if_neg hr, sub_sub_cancel]
    exact hx

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change U 0 ≠ U 1
  have hIoc : Finset.Ioc (0 : ℕ) 1 = {1} := Nat.Ioc_succ_singleton 0
  norm_num [U, Chebyshev.psi_zero, Chebyshev.psi_one, hIoc,
    ArithmeticFunction.vonMangoldt_apply_one]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

def evidence : Registration arena (type_of% @rh_iff_critical_gap_tendsto_atTop) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rh_iff_critical_gap_tendsto_atTop, changed, changed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_critical_gap_tendsto_atTop) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap.rh_iff_critical_gap_tendsto_atTop
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap.evidence
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
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
