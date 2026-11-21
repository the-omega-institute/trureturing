import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedCriticalWidth
import Reg.Support.SingleDependentReadout

/-! The real part of the supplied zero sets both the comparison threshold and
the normalization exponent. An exaggerated real part makes every width have
zero lower mass limit, so there is no finite cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedCriticalWidth
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualData)
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedCriticalWidth

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def exaggeratedRealPart : Realization signature :=
  realize signature (fun _ _ _ => 5 / 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ (ρ : ℂ), IsNontrivialZero ρ →
    let β := V.readout () () ρ
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
      ∃! Wstar : ℝ, 0 < Wstar ∧ ∀ W : ℝ, 0 ≤ W →
        (Filter.liminf
          (fun B : ℝ => (∫ x in B * Real.exp (-W)..B, max (-primeTail x) 0 / Real.sqrt x) /
            B ^ (β - 1 / 2)) atTop = 0 ↔ W ≤ Wstar)

private theorem normalized_mass_at_exaggerated_exponent {W : ℝ} (hW : 0 ≤ W) :
    Tendsto (fun B : ℝ =>
      (∫ x in B * Real.exp (-W)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (2 : ℝ))
      atTop (𝓝 0) := by
  let f (x : ℝ) := max (-primeTail x) 0 / Real.sqrt x
  have htail : Tendsto primeTail atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨X, hX⟩ := eventually_atTop.mp (htail.eventually_const_lt (by norm_num : (-1 : ℝ) < 0))
  have hleft : Tendsto (fun B : ℝ => B * Real.exp (-W)) atTop atTop :=
    tendsto_id.atTop_mul_const (Real.exp_pos _)
  have hbounds : ∀ᶠ B : ℝ in atTop, 0 ≤ (∫ x in B * Real.exp (-W)..B, f x) ∧
      (∫ x in B * Real.exp (-W)..B, f x) ≤ B := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hleft.eventually_ge_atTop (max 1 X)] with B hB hA
    let A := B * Real.exp (-W)
    have hAB : A ≤ B :=
      mul_le_of_le_one_right hB.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hW))
    have hone (x : ℝ) (hx : x ∈ Icc A B) : 1 ≤ x := (le_max_left _ _).trans (hA.trans hx.1)
    have hint : IntervalIntegrable f volume A B :=
      (((prime_integrable.continuousOn_Ici_primitive_Ioi.mono hone).neg.sup
        continuousOn_const).div Real.continuous_sqrt.continuousOn
        (fun x hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hone x hx))).ne')
      ).intervalIntegrable_of_Icc hAB
    refine ⟨intervalIntegral.integral_nonneg_of_forall hAB
      (fun _ => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)), ?_⟩
    calc
      _ ≤ ∫ _ in A..B, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hAB hint intervalIntegrable_const
        intro x hx
        have hs : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (hone x hx)
        have htailx := hX x ((le_max_right _ _).trans (hA.trans hx.1))
        apply (div_le_iff₀ (zero_lt_one.trans_le hs)).2
        rw [one_mul]
        exact (max_le (by linarith only [htailx]) zero_le_one).trans hs
      _ = B - A := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
      _ ≤ B := sub_le_self _ (mul_nonneg hB.le (Real.exp_nonneg _))
  have hdecay : Tendsto (fun B : ℝ => 1 / B) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.congr (fun B => (one_div B).symm)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay ?_ ?_
  · filter_upwards [hbounds, eventually_gt_atTop (0 : ℝ)] with B h hB
    exact div_nonneg h.1 (Real.rpow_nonneg hB.le _)
  · filter_upwards [hbounds, eventually_gt_atTop (0 : ℝ)] with B h hB
    have hratio : B / B ^ (2 : ℝ) = 1 / B := by rw [Real.rpow_two]; field_simp
    exact (div_le_div_of_nonneg_right h.2 (Real.rpow_nonneg hB.le _)).trans_eq hratio

private theorem exaggerated_real_part_fails : ¬ arena.Law exaggeratedRealPart := by
  intro h
  have hm := h (actualData.zero 0) (actualData.zero_isNontrivial 0)
  change ((1 / 2 : ℝ) < 5 / 2 → (∀ z : ℂ, IsNontrivialZero z → z.re ≤ 5 / 2) → _) at hm
  obtain ⟨Wstar, ⟨hWstar, hcut⟩, _⟩ :=
    hm (by norm_num) (fun z hz => hz.2.2.le.trans (by norm_num))
  have h := hcut (Wstar + 1) (by positivity)
  change (Filter.liminf
    (fun B : ℝ => (∫ x in B * Real.exp (-(Wstar + 1))..B, max (-primeTail x) 0 / Real.sqrt x) /
      B ^ ((5 / 2 : ℝ) - 1 / 2)) atTop = 0 ↔ Wstar + 1 ≤ Wstar) at h
  rw [show (5 / 2 : ℝ) - 1 / 2 = 2 by norm_num] at h
  have hle := h.mp (normalized_mass_at_exaggerated_exponent (by positivity)).liminf_eq
  linarith only [hle]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena (type_of% @prime_tail_zero_liminf_iff_le_critical_width) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_zero_liminf_iff_le_critical_width, exaggeratedRealPart,
    exaggerated_real_part_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual exaggeratedRealPart exaggerated_real_part_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_zero_liminf_iff_le_critical_width) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_zero_liminf_iff_le_critical_width "__information_unit"
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
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedCriticalWidth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedCriticalWidth
