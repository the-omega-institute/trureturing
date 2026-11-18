/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/ContinuumWeight
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/ContinuumWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The central moving-weight integral retains the exact kernel cancellation. -/

import D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper MovingWeight

private def kernel (P s t : ℝ) : ℝ := s * P ^ s / (t ^ s + P ^ s)

private lemma kernel_integrable {P s : ℝ} (hP : 0 < P) (hs : 1 < s) :
    IntegrableOn (kernel P s) (Ioi 0) :=
  (power_kernel_integral hs (rpow_pos_of_pos hP s)).1

private lemma kernel_interval {P s a b : ℝ} (hP : 0 < P) (hs : 1 < s)
    (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable (kernel P s) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact (kernel_integrable hP hs).mono_set (fun t ht => ha.trans_lt ht.1)

private lemma left_integral {P s a : ℝ} (hP : 0 < P) (hs : 0 ≤ s)
    (ha : 0 < a) (haP : a ≤ P) :
    (∫ t in a..P, weight P s t) =
      P * log 2 - a * weight P s a - s * (P - a) +
        ∫ t in a..P, kernel P s t := by
  have hPP : 0 < P ^ s := rpow_pos_of_pos hP s
  have hcontL : ContinuousOn (leftWeight P s) (Icc a P) := by
    intro t ht
    exact (leftWeight_deriv hP (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hcontK : ContinuousOn (kernel P s) (Icc a P) := by
    intro t ht
    have ht0 := ha.trans_le ht.1
    exact (continuousAt_const.div
      ((hasDerivAt_rpow_const (Or.inl ht0.ne')).continuousAt.add continuousAt_const)
      (by positivity : t ^ s + P ^ s ≠ 0)).continuousWithinAt
  have hli := hcontL.intervalIntegrable_of_Icc (μ := volume) haP
  have hki := hcontK.intervalIntegrable_of_Icc (μ := volume) haP
  have hFTC : (∫ t in a..P, leftWeight P s t - kernel P s t) =
      (P * leftWeight P s P - s * P) - (a * leftWeight P s a - s * a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hli.sub hki)
    intro t ht
    rw [uIcc_of_le haP] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hd := ((hasDerivAt_id t).mul (leftWeight_deriv hP ht0)).sub
      ((hasDerivAt_id t).const_mul s)
    convert hd using 1
    · funext t; ring
    · dsimp only [kernel, abelKernel]
      field_simp [ht0.ne', (by positivity : t ^ s + P ^ s ≠ 0)]
      <;> ring
  have heq : (∫ t in a..P, leftWeight P s t) = ∫ t in a..P, weight P s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le haP] at ht
    exact leftWeight_eq_weight hP (ha.trans_le ht.1) hs ht.2
  rw [intervalIntegral.integral_sub hli hki, heq, leftWeight_at_cutoff hP,
    leftWeight_eq_weight hP ha hs haP] at hFTC
  linarith

private lemma right_integral {P s b : ℝ} (hP : 0 < P) (hs : 0 ≤ s)
    (hPb : P ≤ b) :
    (∫ t in P..b, weight P s t) =
      b * weight P s b - P * log 2 + ∫ t in P..b, kernel P s t := by
  have hPP : 0 < P ^ s := rpow_pos_of_pos hP s
  have hcontR : ContinuousOn (logWeight s (P ^ s)) (Icc P b) := by
    intro t ht
    exact (logWeight_deriv hPP (hP.trans_le ht.1)).continuousAt.continuousWithinAt
  have hcontK : ContinuousOn (kernel P s) (Icc P b) := by
    intro t ht
    have ht0 := hP.trans_le ht.1
    exact (continuousAt_const.div
      ((hasDerivAt_rpow_const (Or.inl ht0.ne')).continuousAt.add continuousAt_const)
      (by positivity : t ^ s + P ^ s ≠ 0)).continuousWithinAt
  have hri := hcontR.intervalIntegrable_of_Icc (μ := volume) hPb
  have hki := hcontK.intervalIntegrable_of_Icc (μ := volume) hPb
  have hFTC : (∫ t in P..b, logWeight s (P ^ s) t - kernel P s t) =
      b * logWeight s (P ^ s) b - P * logWeight s (P ^ s) P := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hri.sub hki)
    intro t ht
    rw [uIcc_of_le hPb] at ht
    have ht0 : 0 < t := hP.trans_le ht.1
    have hd := (hasDerivAt_id t).mul (logWeight_deriv hPP ht0)
    convert hd using 1
    · funext t; ring
    · dsimp only [kernel, abelKernel]
      field_simp [ht0.ne', (by positivity : t ^ s + P ^ s ≠ 0)]
      <;> ring
  have heq : (∫ t in P..b, logWeight s (P ^ s) t) = ∫ t in P..b, weight P s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hPb] at ht
    exact rightWeight_eq_weight hP (hP.trans_le ht.1) hs ht.1
  rw [intervalIntegral.integral_sub hri hki, heq, rightWeight_at_cutoff hP,
    rightWeight_eq_weight hP (hP.trans_le hPb) hs hPb] at hFTC
  linarith

private lemma weight_interval {P s a b : ℝ} (hP : 0 < P) (hs : 0 ≤ s)
    (ha : 0 < a) (haP : a ≤ P) (hPb : P ≤ b) :
    IntervalIntegrable (weight P s) volume a b := by
  have hl : IntervalIntegrable (weight P s) volume a P := by
    have h : ContinuousOn (leftWeight P s) (Icc a P) := by
      intro t ht
      exact (leftWeight_deriv hP (ha.trans_le ht.1)).continuousAt.continuousWithinAt
    apply (h.intervalIntegrable_of_Icc (μ := volume) haP).congr_uIoo
    intro t ht
    rw [uIoo_of_le haP] at ht
    exact leftWeight_eq_weight hP (ha.trans ht.1) hs ht.2.le
  have hr : IntervalIntegrable (weight P s) volume P b := by
    have h : ContinuousOn (logWeight s (P ^ s)) (Icc P b) := by
      intro t ht
      exact (logWeight_deriv (rpow_pos_of_pos hP s)
        (hP.trans_le ht.1)).continuousAt.continuousWithinAt
    apply (h.intervalIntegrable_of_Icc (μ := volume) hPb).congr_uIoo
    intro t ht
    rw [uIoo_of_le hPb] at ht
    exact rightWeight_eq_weight hP (hP.trans ht.1) hs ht.1.le
  exact hl.trans hr

private lemma kernel_head_lower {P s : ℝ} (hP : 0 < P) (hs : 1 < s) :
    (P / 2) * s * (1 - (2 : ℝ) ^ (-s)) ≤ ∫ t in (0 : ℝ)..(P / 2), kernel P s t := by
  have hs0 : 0 ≤ s := (zero_lt_one.trans hs).le
  have hPP : 0 < P ^ s := rpow_pos_of_pos hP s
  have hq : (P / 2) ^ s = P ^ s * (2 : ℝ) ^ (-s) := by
    rw [div_rpow hP.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
      rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hk := kernel_interval hP hs (le_refl (0 : ℝ)) (by positivity : (0 : ℝ) ≤ P / 2)
  have hh : ∀ t ∈ Ioo (0 : ℝ) (P / 2), s * (1 - (2 : ℝ) ^ (-s)) ≤ kernel P s t := by
    intro t ht
    have htp : 0 < t ^ s := rpow_pos_of_pos ht.1 s
    have htP : t ^ s ≤ P ^ s * (2 : ℝ) ^ (-s) := by
      rw [← hq]
      exact rpow_le_rpow ht.1.le ht.2.le hs0
    have hratio : t ^ s / (t ^ s + P ^ s) ≤ (2 : ℝ) ^ (-s) := by
      calc
        _ ≤ t ^ s / P ^ s := div_le_div_of_nonneg_left htp.le hPP (by linarith)
        _ ≤ _ := (div_le_iff₀ hPP).mpr (by nlinarith only [htP])
    have hid : kernel P s t = s * (1 - t ^ s / (t ^ s + P ^ s)) := by
      dsimp only [kernel]
      field_simp [(by positivity : t ^ s + P ^ s ≠ 0)]
      <;> ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hratio 1) hs0
  have h := intervalIntegral.integral_mono_on_of_le_Ioo
    (by positivity : (0 : ℝ) ≤ P / 2) intervalIntegrable_const hk hh
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_assoc] using h

private lemma kernel_middle_upper {P s : ℝ} (hP : 0 < P) (hs : 1 < s) :
    (∫ t in (P / 2)..(2 * P), kernel P s t) ≤
      π * P / sin (π / s) - s * (P / 2) +
        s * (P / 2) * (2 : ℝ) ^ (-s) := by
  have hki := kernel_integrable hP hs
  have hk0 := kernel_interval hP hs (le_refl (0 : ℝ)) (by positivity : (0 : ℝ) ≤ P / 2)
  have hkm := kernel_interval hP hs (by positivity : (0 : ℝ) ≤ P / 2)
    (by linarith : P / 2 ≤ 2 * P)
  have hwhole : (∫ t in (0 : ℝ)..(2 * P), kernel P s t) ≤
      ∫ t in Ioi (0 : ℝ), kernel P s t := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * P)]
    apply setIntegral_mono_set hki
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp only [kernel]
      positivity
    · exact Eventually.of_forall (fun t ht => ht.1)
  have heval := (power_kernel_integral hs (rpow_pos_of_pos hP s)).2
  have hexp : (P ^ s) ^ (1 / s) = P := by
    rw [← rpow_mul hP.le, mul_one_div_cancel (by linarith : s ≠ 0), rpow_one]
  rw [hexp] at heval
  change (∫ t in Ioi (0 : ℝ), kernel P s t) = _ at heval
  rw [heval, ← intervalIntegral.integral_add_adjacent_intervals hk0 hkm] at hwhole
  have hhead := kernel_head_lower hP hs
  nlinarith only [hwhole, hhead]

/-- The central continuum mass has the exact beta-kernel correction; the
two removed tails cost only an exponentially small quantity. -/
theorem central_integral_upper {P s : ℝ} (hP : 0 < P) (hs : 1 < s) :
    (∫ t in (P / 2)..(2 * P), weight P s t) ≤
      P * (π / sin (π / s) - s) + (s / 2 + 2) * P * (2 : ℝ) ^ (-s) := by
  have hs0 : 0 ≤ s := (zero_lt_one.trans hs).le
  have ha : 0 < P / 2 := by positivity
  have haP : P / 2 ≤ P := by linarith
  have hPb : P ≤ 2 * P := by linarith
  have hwi := weight_interval hP hs0 ha haP hPb
  have hwL := weight_interval hP hs0 ha haP (le_refl P)
  have hwR := weight_interval hP hs0 hP (le_refl P) hPb
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hwL hwR
  rw [left_integral hP hs0 ha haP, right_integral hP hs0 hPb] at hsplit
  have hkiL := kernel_interval hP hs ha.le haP
  have hkiR := kernel_interval hP hs hP.le hPb
  have hksplit := intervalIntegral.integral_add_adjacent_intervals hkiL hkiR
  have htail : weight P s (2 * P) ≤ (2 : ℝ) ^ (-s) := by
    rw [← rightWeight_eq_weight hP (by positivity : 0 < 2 * P) hs0 hPb]
    dsimp only [logWeight]
    have hpow : P ^ s / (2 * P) ^ s = (2 : ℝ) ^ (-s) := by
      rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP.le,
        div_mul_eq_div_div, div_self (rpow_pos_of_pos hP s).ne', one_div,
        ← rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hpow]
    have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + (2 : ℝ) ^ (-s))
    linarith
  have hk := kernel_middle_upper hP hs
  have hhead := weight_nonneg P s (P / 2)
  have ht := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * P)
  nlinarith only [hsplit, hksplit, hk, hhead, ht, mul_nonneg ha.le hhead]

end D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight
