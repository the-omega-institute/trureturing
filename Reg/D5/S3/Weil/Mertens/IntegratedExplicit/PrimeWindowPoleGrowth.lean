import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

/-- The actual zeta value in the incoming zero hypothesis. -/
def actual : Realization signature :=
  realize signature (fun _ _ z => riemannZeta z) (fun e => nomatch e)

def allZeros : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {z₀ : ℂ} (_ : V.readout () () z₀ = 0) (_ : 1/2 < z₀.re)
    {b ε : ℝ} (_ : 1 < b) (_ : 0 < ε),
    ∀ᶠ Y : ℝ in atTop, Y^(b*(z₀.re-1/2)-ε) ≤
      ∫ x in Y..Y^b, max (-primeTail x) 0 / Real.sqrt x

private theorem all_zeros_fails : ¬ arena.Law allZeros := by
  intro h
  have hbad := h (z₀ := 3) rfl (by norm_num) (b := 2) (ε := 1) (by norm_num) (by norm_num)
  have hlim : Tendsto primeTail atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨X, hX⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hlim 1 one_pos)
  obtain ⟨Y, hbad, hY, hX'⟩ := (hbad.and ((eventually_gt_atTop (2 : ℝ)).and
    (eventually_ge_atTop X))).exists
  norm_num at hbad
  have hYs : Y ≤ Y^2 := by nlinarith
  have bound : ∀ x ∈ Ι Y (Y^2), ‖max (-primeTail x) 0 / Real.sqrt x‖ ≤ 1 := by
    intro x hx
    rw [Set.uIoc_of_le hYs] at hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have hnorm := hX x (hX'.trans hx.1.le)
    rw [Real.dist_eq, sub_zero, abs_lt] at hnorm
    have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))]
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt x)).2
    rw [one_mul]
    exact max_le (by linarith [hnorm.1]) (Real.sqrt_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const bound
  rw [Real.norm_eq_abs, one_mul, abs_of_nonneg (sub_nonneg.mpr hYs)] at hi
  have hgrowth : Y ^ 2 < Y ^ 4 := by
    exact pow_lt_pow_right₀ (by linarith) (by omega)
  linarith [le_abs_self (∫ x in Y..Y^2, max (-primeTail x) 0 / Real.sqrt x)]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, -2, ?_⟩
  change riemannZeta 0 ≠ riemannZeta (-2)
  have hz : riemannZeta (-2) = 0 := by simpa using riemannZeta_neg_two_mul_nat_add_one 0
  rw [hz, riemannZeta_zero]
  norm_num

def family : Registration arena (type_of% @off_line_zero_forces_window_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@off_line_zero_forces_window_mass, allZeros, all_zeros_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual allZeros all_zeros_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@off_line_zero_forces_window_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth.off_line_zero_forces_window_mass
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => riemannZeta z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Criterion

abbrev powerSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def power : Realization powerSignature :=
  realize powerSignature (fun _ η Y => Y^η) (fun e => nomatch e)

def criterionArena : Arena where
  signature := powerSignature
  Law V := ∀ {b : ℝ}, 1 < b → (RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop,
    (∫ x in Y..Y^b, max (-primeTail x) 0 / Real.sqrt x) ≤ V.readout () η Y)

private def changed : Realization powerSignature := by
  classical
  exact realize powerSignature (fun _ _ Y => if RiemannHypothesis then -1 else
    ∫ x in Y..Y^(2 : ℝ), max (-primeTail x) 0 / Real.sqrt x) (fun e => nomatch e)

private lemma changed_fails : ¬ criterionArena.Law changed := by
  classical
  intro H
  have h := H (b := 2) (by norm_num)
  by_cases hr : RiemannHypothesis
  · have hf := h.mp hr 1 one_pos
    obtain ⟨Y, hY, hY1⟩ := (hf.and_eventually (eventually_gt_atTop (1 : ℝ))).exists
    change _ ≤ (if RiemannHypothesis then -1 else _) at hY
    simp only [hr, ↓reduceIte] at hY
    have hi : 0 ≤ ∫ x in Y..Y^(2 : ℝ), max (-primeTail x) 0 / Real.sqrt x :=
      intervalIntegral.integral_nonneg (by rw [Real.rpow_two]; nlinarith)
        (fun x _ => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
    linarith
  · apply hr
    apply h.mpr
    intro η _
    apply Filter.Eventually.frequently
    filter_upwards with Y
    change _ ≤ (if RiemannHypothesis then -1 else _)
    simp [hr]

def evidence : Registration criterionArena (type_of% @rh_iff_frequently_small_prime_windows) where
  actual := power
  bridge := Iff.rfl
  variation := ⟨@rh_iff_frequently_small_prime_windows, changed, changed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    criterionArena.Law power changed changed_fails
  dependence := by
    intro _
    refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ)^(1 : ℝ) ≠ 1^(1 : ℝ)
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rh_iff_frequently_small_prime_windows) (Realization powerSignature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth.rh_iff_frequently_small_prime_windows
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth.Criterion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨criterionArena⟩
  objectArena := .source ⟨criterionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source criterionArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize powerSignature (fun _ η Y => Y^η) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body","body","arg","body","body","fn","arg","body","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Criterion

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
