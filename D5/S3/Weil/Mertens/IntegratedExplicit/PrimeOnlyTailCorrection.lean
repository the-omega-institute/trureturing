/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime powers contribute exactly two at the square-root tail scale and at most a logarithmic loss in critical negative-part windows. -/

import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.Robin.CompleteMertensPeak
import D5.S3.Weil.Mertens.WeightedPrimeLimit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Real Filter
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Arith.Robin.EulerLayerRootCorrection (psi_theta_root_limit)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection

/-- The tail of the Chebyshev error with weight one per prime. -/
def primeTail (x : ℝ) : ℝ := ∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2

private def diffKernel (t : ℝ) : ℝ := (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2

private def rootKernel (t : ℝ) : ℝ := Real.sqrt t / t ^ 2

private lemma rootKernel_rpow {t : ℝ} (ht : 0 < t) :
    rootKernel t = t ^ (-(3 / 2) : ℝ) := by
  rw [show (-(3 / 2) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub ht,
    Real.rpow_two, ← Real.sqrt_eq_rpow]
  rfl

private lemma root_integrable {x : ℝ} (hx : 0 < x) : IntegrableOn rootKernel (Ioi x) :=
  (integrableOn_Ioi_rpow_of_lt (a := (-(3/2) : ℝ)) (by norm_num) hx).congr_fun
    (fun _ ht => (rootKernel_rpow (hx.trans ht)).symm) measurableSet_Ioi

private lemma root_integral {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi x, rootKernel t = 2 / Real.sqrt x := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun _ ht => rootKernel_rpow (hx.trans ht)),
    integral_Ioi_rpow_of_lt (by norm_num) hx, show (-(3/2) : ℝ) + 1 = -(1/2) by norm_num,
    Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  ring

private lemma diff_integrable : IntegrableOn diffKernel (Ioi 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  apply ((root_integrable one_pos).const_mul C).mono'
    ((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
  change ‖(Chebyshev.psi t - Chebyshev.theta t) / t ^ 2‖ ≤ C * rootKernel t
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t))
    (sq_nonneg t))]
  exact (div_le_div_of_nonneg_right (hC t) (sq_nonneg t)).trans_eq (by dsimp [rootKernel]; ring)

private lemma prime_integrable :
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) (Ioi 1) := by
  apply (chebyshev_error_kernel_integrable.sub diff_integrable).congr_fun _ measurableSet_Ioi
  intro t _
  dsimp [diffKernel]
  ring

private lemma tail_eq {x : ℝ} (hx : 1 ≤ x) :
    Q x - primeTail x = ∫ t in Ioi x, diffKernel t := by
  change (∫ t in Ioi x, (Chebyshev.psi t - t) / t ^ 2) -
    (∫ t in Ioi x, (Chebyshev.theta t - t) / t ^ 2) = _
  rw [← integral_sub
    (chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi hx))
    (prime_integrable.mono_set (Ioi_subset_Ioi hx))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp [diffKernel, Arith.Robin.CompleteMertensPeak.psiErrorKernel]
  ring

private lemma integral_sandwich {x L H : ℝ} (hx : 1 ≤ x)
    (h : ∀ t, x < t → L * Real.sqrt t ≤ Chebyshev.psi t - Chebyshev.theta t ∧
      Chebyshev.psi t - Chebyshev.theta t ≤ H * Real.sqrt t) :
    L * (2 / Real.sqrt x) ≤ Q x - primeTail x ∧
      Q x - primeTail x ≤ H * (2 / Real.sqrt x) := by
  have hx0 := zero_lt_one.trans_le hx
  have hi := diff_integrable.mono_set (Ioi_subset_Ioi hx)
  have hr := root_integrable hx0
  rw [tail_eq hx, ← root_integral hx0, ← integral_const_mul, ← integral_const_mul]
  constructor
  · apply setIntegral_mono_on (hr.const_mul _) hi measurableSet_Ioi
    intro t ht
    simpa [diffKernel, rootKernel, mul_div_assoc] using
      div_le_div_of_nonneg_right (h t ht).1 (sq_nonneg t)
  · apply setIntegral_mono_on hi (hr.const_mul _) measurableSet_Ioi
    intro t ht
    simpa [diffKernel, rootKernel, mul_div_assoc] using
      div_le_div_of_nonneg_right (h t ht).2 (sq_nonneg t)

private lemma scaled_limit :
    Tendsto (fun x => Real.sqrt x * (Q x - primeTail x)) atTop (𝓝 2) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp psi_theta_root_limit)
    (ε / 4) (by positivity))
  filter_upwards [eventually_ge_atTop (max T 1)] with x hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hs := integral_sandwich (L := 1 - ε / 4) (H := 1 + ε / 4) hx1 (by
    intro t ht
    have hs0 := Real.sqrt_pos.mpr (hx0.trans ht)
    have hp := hT t ((le_max_left _ _).trans (hx.trans ht.le))
    rw [Real.dist_eq, abs_lt] at hp
    exact ⟨((le_div_iff₀ hs0).mp (by linarith)), ((div_le_iff₀ hs0).mp (by linarith))⟩)
  have hs0 := Real.sqrt_pos.mpr hx0
  have hl := mul_le_mul_of_nonneg_left hs.1 hs0.le
  have hu := mul_le_mul_of_nonneg_left hs.2 hs0.le
  rw [Real.dist_eq, abs_lt]
  field_simp [hs0.ne'] at hl hu
  constructor <;> linarith

private lemma pointwise_bound {C : ℝ} (hC : ∀ t, 1 ≤ t →
    Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Q x - primeTail x ∧ Q x - primeTail x ≤ 2 * C / Real.sqrt x := by
  have hs := integral_sandwich (L := 0) (H := C) hx (fun t ht =>
    ⟨by simpa using Chebyshev.theta_le_psi t, hC t (hx.trans ht.le)⟩)
  exact ⟨by simpa only [zero_mul] using hs.1, hs.2.trans_eq (by ring)⟩

private lemma window_bound {C a b : ℝ} (hC : ∀ t, 1 ≤ t →
    Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t) (ha : 1 ≤ a) (hab : a ≤ b) :
    let W := ∫ x in a..b, (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x
    0 ≤ W ∧ W ≤ 2 * C * Real.log (b / a) := by
  dsimp only
  have hmem (x : ℝ) (hx : x ∈ uIcc a b) : 1 ≤ x := by
    rw [uIcc_of_le hab] at hx
    exact ha.trans hx.1
  have hp : ContinuousOn primeTail (uIcc a b) :=
    prime_integrable.continuousOn_Ici_primitive_Ioi.mono (fun x hx => hmem x hx)
  have hq : ContinuousOn Q (uIcc a b) :=
    chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi.mono (fun x hx => hmem x hx)
  have hi : IntervalIntegrable (fun x => (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x)
      volume a b := (((hp.neg.sup (continuousOn_const (c := (0 : ℝ)))).sub
    (hq.neg.sup (continuousOn_const (c := (0 : ℝ))))).div
    Real.continuous_sqrt.continuousOn (fun x hx => (Real.sqrt_pos.mpr
      (zero_lt_one.trans_le (hmem x hx))).ne')).intervalIntegrable (μ := volume)
  have hxpos (x : ℝ) (hx : x ∈ uIcc a b) := zero_lt_one.trans_le (hmem x hx)
  have hinv : ContinuousOn (fun x : ℝ => 2 * C * x⁻¹) (uIcc a b) :=
    continuousOn_const.mul (continuousOn_id.inv₀ fun x hx => (hxpos x hx).ne')
  have horder (x : ℝ) (hx : x ∈ Icc a b) :
      0 ≤ (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x ∧
      (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x ≤ 2 * C * x⁻¹ := by
    have hx1 := ha.trans hx.1
    have h := pointwise_bound hC hx1
    have ht : primeTail x ≤ Q x := by linarith [h.1]
    have hgap : max (-primeTail x) 0 - max (-Q x) 0 ≤ Q x - primeTail x := by
      rcases le_total (Q x) 0 with hq0 | hq0 <;> rcases le_total (primeTail x) 0 with hp0 | hp0
        <;> simp [max_def] <;> split_ifs <;> linarith
    have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx1)
    refine ⟨div_nonneg (sub_nonneg.mpr (max_le_max (neg_le_neg ht) le_rfl)) hs0.le,
      (div_le_div_of_nonneg_right (hgap.trans h.2) hs0.le).trans_eq ?_⟩
    rw [div_div, ← sq, Real.sq_sqrt (zero_le_one.trans hx1), div_eq_mul_inv]
  refine ⟨intervalIntegral.integral_nonneg hab (fun x hx => (horder x hx).1), ?_⟩
  calc
    _ ≤ ∫ x in a..b, 2 * C * x⁻¹ := intervalIntegral.integral_mono_on hab hi
      hinv.intervalIntegrable (fun x hx => (horder x hx).2)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_inv (fun h => (hxpos 0 h).false)]

/-- The exact root-scale correction and the cost of suppressing prime powers in
critical negative-part windows, for every Chebyshev majorant on the same domain. -/
theorem prime_power_window_correction :
    Tendsto (fun x => Real.sqrt x * (Q x - primeTail x)) atTop (𝓝 2) ∧
    ∀ C : ℝ, (∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t) →
      (∀ x, 1 ≤ x → 0 ≤ Q x - primeTail x ∧ Q x - primeTail x ≤ 2 * C / Real.sqrt x) ∧
      ∀ a b : ℝ, 1 ≤ a → a ≤ b →
        let W := ∫ x in a..b, (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x
        0 ≤ W ∧ W ≤ 2 * C * Real.log (b / a) :=
  ⟨scaled_limit, fun _ hC => ⟨fun _ => pointwise_bound hC, fun _ _ => window_bound hC⟩⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
