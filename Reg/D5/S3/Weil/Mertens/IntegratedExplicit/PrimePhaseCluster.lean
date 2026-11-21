import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
import Reg.Support.SingleDependentReadout

/-! Intervening on the real-part readout changes both the normalization and the selected zeros. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Complex.re) (fun e => nomatch e)

def exaggeratedRealPart : Realization signature :=
  realize signature (fun _ _ _ => 5 / 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ (ρ : ℂ), IsNontrivialZero ρ →
    let realPart := V.readout () ()
    let β := realPart ρ
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    ∀ (W : ℝ), 0 < W → ∀ (y : ℝ),
    MapClusterPt y atTop (fun B : ℝ =>
      (∫ x in B * Real.exp (-W)..B, max (-primeTail x) 0 / Real.sqrt x) /
        B ^ (β - 1 / 2)) ↔
    ∃ h ∈ closure (range phaseOrbit), y = phaseWindow realPart β W h

private theorem high_scale_mass_tendsto_zero :
    Tendsto (fun B : ℝ =>
      (∫ x in B * Real.exp (-1)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have htail : Tendsto primeTail atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (htail.eventually_const_lt (show (-1 : ℝ) < 0 by norm_num))
  have he := Real.exp_pos (-1)
  have he₁ := Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
  refine squeeze_zero_norm' ?_
    (tendsto_inv_atTop_zero : Tendsto (fun B : ℝ => B⁻¹) atTop (𝓝 0))
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (max 1 X / Real.exp (-1))] with B hB hleft
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  have hleft' := (div_le_iff₀ he).1 hleft
  have hAB : B * Real.exp (-1) ≤ B := mul_le_of_le_one_right hB₀.le he₁
  have hbound : ‖∫ x in B * Real.exp (-1)..B, max (-primeTail x) 0 / Real.sqrt x‖ ≤ B := by
    calc
      _ ≤ (1 : ℝ) * |B - B * Real.exp (-1)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [uIoc_of_le hAB] at hx
        have hx₁ : 1 ≤ x := (le_max_left _ _).trans (hleft'.trans hx.1.le)
        have hs : 1 ≤ Real.sqrt x := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt hx₁
        have ht := hX x ((le_max_right _ _).trans (hleft'.trans hx.1.le))
        rw [Real.norm_eq_abs, abs_of_nonneg
          (div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))]
        exact (div_le_one (zero_lt_one.trans_le hs)).2
          ((max_le (by linarith only [ht]) zero_le_one).trans hs)
      _ ≤ B := by
        rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hAB)]
        exact sub_le_self B (mul_nonneg hB₀.le he.le)
  calc
    _ = ‖∫ x in B * Real.exp (-1)..B, max (-primeTail x) 0 / Real.sqrt x‖ / B ^ 2 := by
      rw [norm_div, Real.norm_of_nonneg (sq_nonneg B)]
    _ ≤ B / B ^ 2 := div_le_div_of_nonneg_right hbound (sq_nonneg _)
    _ = B⁻¹ := by field_simp

private theorem exaggerated_window_positive :
    0 < phaseWindow (fun _ => 5 / 2) (5 / 2) 1 (1 : ℕ → Circle) := by
  let series (u : ℝ) := ∑' k : ℕ, actualCoeff k * (phaseOrbit u k : ℂ)
  have hseries : Continuous series := by
    apply continuous_tsum (fun k => by unfold phaseOrbit; fun_prop)
      actualCoeff_hasSum.summable.norm
    intro k u
    simp only [norm_mul, Circle.norm_coe, mul_one, le_refl]
  have hzero : 0 < (series 0).re := by
    have hsum := Complex.hasSum_re actualCoeff_hasSum
    have hpos (k : ℕ) : 0 < (actualCoeff k).re := by
      have hk := actualData.zero_isNontrivial (actualOccurrenceEquiv k).1
      exact (heightRefinement_pairWeight_strip hk.2.1 hk.2.2).1
    simp only [series, phaseOrbit, zero_mul, Circle.exp_zero, Circle.coe_one, mul_one,
      actualCoeff_hasSum.tsum_eq, Complex.ofReal_re]
    simpa only [hsum.tsum_eq, Complex.ofReal_re] using
      hsum.summable.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  have hfun (s : ℝ) :
      max (-phaseProfile (fun _ => 5 / 2) (5 / 2) (1 : ℕ → Circle) (-s)) 0 =
        max (series (-s)).re 0 := by
    simp [phaseProfile, rightmostCoeff, series]
  unfold phaseWindow
  simp_rw [hfun]
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
  · have hw : Continuous (fun s : ℝ => Real.exp (-((5 : ℝ) / 2 - 1 / 2) * s)) := by fun_prop
    exact (hw.mul ((Complex.continuous_re.comp (hseries.comp continuous_neg)).max
      continuous_const)).continuousOn
  · exact fun _ _ => mul_nonneg (Real.exp_nonneg _) (le_max_right _ _)
  · refine ⟨0, by simp, ?_⟩
    rw [neg_zero]
    exact mul_pos (Real.exp_pos _) (hzero.trans_le (le_max_left _ 0))

private theorem exaggerated_real_part_fails : ¬ arena.Law exaggeratedRealPart := by
  intro law
  let y := phaseWindow (fun _ => 5 / 2) (5 / 2) 1 (1 : ℕ → Circle)
  have hy : 0 < y := exaggerated_window_positive
  have hone : (1 : ℕ → Circle) ∈ closure (range phaseOrbit) := by
    apply subset_closure
    refine ⟨0, ?_⟩
    funext k
    simp [phaseOrbit]
  have hcluster := (law (actualData.zero 0) (actualData.zero_isNontrivial 0)
    (by norm_num [exaggeratedRealPart, realize]) (fun _ _ => le_rfl) 1 (by norm_num) y).2
    ⟨1, hone, rfl⟩
  change MapClusterPt y atTop (fun B : ℝ =>
    (∫ x in B * Real.exp (-1)..B, max (-primeTail x) 0 / Real.sqrt x) /
      B ^ ((5 : ℝ) / 2 - 1 / 2)) at hcluster
  rw [show (5 : ℝ) / 2 - 1 / 2 = 2 by norm_num] at hcluster
  simp only [Real.rpow_two] at hcluster
  obtain ⟨_, hl, hu⟩ := ((hcluster.frequently (lt_mem_nhds (half_lt_self hy))).and_eventually
    (high_scale_mass_tendsto_zero.eventually_lt_const (half_pos hy))).exists
  exact hl.not_gt hu

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena (type_of% @prime_tail_mass_cluster_iff_of_attained_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_mass_cluster_iff_of_attained_zero, exaggeratedRealPart,
    exaggerated_real_part_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual exaggeratedRealPart exaggerated_real_part_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_mass_cluster_iff_of_attained_zero) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_mass_cluster_iff_of_attained_zero "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Complex.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
