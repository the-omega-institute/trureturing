/- GID: D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A strict Mertens product gap absorbs every fixed positive-power Euler tail. -/

import D5.S3.Arith.Robin.Analytic.ExceptionCount.Mertens
import D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Set MeasureTheory Asymptotics Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap
open PrimeCutoff

/-- The initial inverse Euler product. -/
def product (P : ℝ) : ℝ :=
  ∏ p ∈ (Finset.Ioc 0 ⌊P⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹

private lemma product_eq {P : ℝ} (hP : 1 < P) :
    product P = exp eulerMascheroniConstant * log P * exp (-_root_.Mertens.E₃ P) := by
  rw [product, Finset.prod_inv_distrib, _root_.Mertens.prod_one_minus_div_prime_eq hP]
  rw [Real.exp_neg, Real.exp_neg]
  field_simp <;> ring

private lemma log_cutoff (t : ℝ) : log (cutoff t) = t - 1 / (2 * t) := log_exp _

private lemma cutoff_log_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 < log (cutoff t) ∧ t / 2 ≤ log (cutoff t) ∧ log (cutoff t) ≤ t := by
  rw [log_cutoff]
  have hi : 0 < 1 / (2 * t) := by positivity
  have hb : 1 / (2 * t) ≤ t / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * t)).mpr
    nlinarith
  exact ⟨by linarith, by linarith, by linarith⟩

private lemma power_tail_small {a : ℝ} (ha : 0 < a) (C : ℝ) :
    Tendsto (fun t : ℝ => C * (cutoff t) ^ (-a) * t ^ 2) atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := tendsto_id.const_div_atTop 1
  have he : Tendsto (fun t : ℝ => exp (a / (2 * t))) atTop (𝓝 1) := by
    have h := ((hi.div_const 2).const_mul a).rexp
    norm_num at h
    convert h using 1
    ext t
    congr 1
    ring
  have hr : Tendsto (fun t : ℝ => t ^ 2 * exp (-a * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha
  have h := ((hr.mul he).const_mul C)
  norm_num at h
  apply h.congr'
  filter_upwards [] with t
  rw [cutoff, Real.rpow_def_of_pos (exp_pos _), log_exp,
    show (t - 1 / (2 * t)) * (-a) = -a * t + a / (2 * t) by ring, exp_add]
  ring

/-- A fixed power-decaying Euler tail is absorbed by the strict logarithmic gap. -/
private theorem product_power_gap {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ t : ℝ in atTop,
      product (cutoff t) * exp (C * (cutoff t) ^ (-a)) ≤
        exp eulerMascheroniConstant * (t - 1 / (4 * t)) := by
  have hE := Mertens.strengthened_mertens.def (by norm_num : (0 : ℝ) < 1 / 128)
  have hn : Tendsto (fun t : ℝ => ‖C * cutoff t ^ (-a) * t ^ 2‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using (power_tail_small ha C).norm
  have hsmall := hn.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1 / 32)
  filter_upwards [cutoff_top.eventually hE, hsmall, eventually_ge_atTop (1 : ℝ)] with t hEt htail ht
  have ht0 : 0 < t := by linarith
  have hlogs := cutoff_log_bounds ht
  have hlog0 : 0 < log (cutoff t) := hlogs.1
  have hP : 1 < cutoff t := (log_pos_iff (exp_pos _).le).mp hlogs.1
  have hE' : |_root_.Mertens.E₃ (cutoff t)| ≤ 1 / (32 * t ^ 2) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / log (cutoff t) ^ 2)] at hEt
    apply hEt.trans
    have hs : t ^ 2 / 4 ≤ log (cutoff t) ^ 2 := by nlinarith [sq_nonneg (log (cutoff t) - t / 2)]
    calc
      (1 / 128 : ℝ) * (1 / log (cutoff t) ^ 2) = 1 / (128 * log (cutoff t) ^ 2) := by ring
      _ ≤ 1 / (32 * t ^ 2) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have htail' : |C * (cutoff t) ^ (-a)| ≤ 1 / (32 * t ^ 2) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)] at htail
    exact (le_div_iff₀ (by positivity : 0 < 32 * t ^ 2)).mpr (by nlinarith)
  let z := -_root_.Mertens.E₃ (cutoff t) + C * (cutoff t) ^ (-a)
  have hz : |z| ≤ 1 / (16 * t ^ 2) := by
    dsimp [z]
    have hh := (abs_add_le (-_root_.Mertens.E₃ (cutoff t)) (C * (cutoff t) ^ (-a)))
    rw [abs_neg] at hh
    calc
      _ ≤ |_root_.Mertens.E₃ (cutoff t)| + |C * cutoff t ^ (-a)| := hh
      _ ≤ 1 / (32 * t ^ 2) + 1 / (32 * t ^ 2) := add_le_add hE' htail'
      _ = _ := by ring
  have hz1 : |z| ≤ 1 := hz.trans (by
    apply (div_le_one (by positivity : 0 < 16 * t ^ 2)).mpr
    nlinarith)
  have hexp : exp z ≤ 1 + 1 / (8 * t ^ 2) := by
    have hh := abs_exp_sub_one_le hz1
    have hh' := (le_abs_self (exp z - 1)).trans hh
    have hh'' := hh'.trans (mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 2))
    have heq : 2 * (1 / (16 * t ^ 2)) = 1 / (8 * t ^ 2) := by ring
    rw [heq] at hh''
    linarith
  rw [product_eq hP, mul_assoc (exp eulerMascheroniConstant * log (cutoff t)), ← exp_add]
  change exp eulerMascheroniConstant * log (cutoff t) * exp z ≤ _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  calc
    log (cutoff t) * exp z ≤ log (cutoff t) * (1 + 1 / (8 * t ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp hlogs.1.le
    _ ≤ t - 1 / (4 * t) := by
      rw [log_cutoff]
      field_simp [ht0.ne']
      nlinarith [sq_nonneg t]

private lemma lower_half_loglog :
    ∀ᶠ x : ℝ in atTop,
      log (log x) - 1 / (4 * log (log x)) < log (log (x / 2)) := by
  have hi : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) := tendsto_id.const_div_atTop 1
  have hr : Tendsto (fun u : ℝ => u / (u - log 2)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).div
      ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub (hi.const_mul (log 2)))
        (by norm_num : (1 : ℝ) - log 2 * 0 ≠ 0)
    norm_num at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (log 2)] with u hu
    have hu0 : u ≠ 0 := by have := log_pos (by norm_num : (1 : ℝ) < 2); linarith
    dsimp only [Pi.div_apply, Pi.sub_apply]
    change (1 : ℝ) / (1 - log 2 * u⁻¹) = u / (u - log 2)
    field_simp [hu0, (sub_pos.mpr hu).ne']
  have hh := (((isLittleO_log_id_atTop).tendsto_div_nhds_zero.mul hr).const_mul (log 2)).comp
    tendsto_log_atTop
  norm_num at hh
  have hs := hh.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hs, eventually_gt_atTop (exp (exp 1))] with x hsmall hx
  have hx0 : 0 < x := (exp_pos _).trans hx
  have hL : exp 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hL1 : 1 < log x := (one_lt_exp_iff.mpr zero_lt_one).trans hL
  have ht : 0 < log (log x) := log_pos hL1
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2one : log (2 : ℝ) < 1 := by
    have hh := log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at hh
    exact hh
  have hden : 0 < log x - log 2 := by linarith
  have hquot : 0 < log x / (log x - log 2) := div_pos (by linarith) hden
  have htangent := log_le_sub_one_of_pos hquot
  rw [Real.log_div (by linarith : log x ≠ 0) hden.ne'] at htangent
  have hdifference : log (log x) - log (log x - log 2) ≤ log 2 / (log x - log 2) := by
    convert htangent using 1
    field_simp [hden.ne']
    ring
  have hbound : log 2 / (log x - log 2) < 1 / (4 * log (log x)) := by
    have heq : log 2 * (log (log x) / log x * (log x / (log x - log 2))) =
        log (log x) * (log 2 / (log x - log 2)) := by
      field_simp [show log x ≠ 0 by linarith]
    dsimp only [Function.comp_def] at hsmall
    rw [heq] at hsmall
    apply (lt_div_iff₀ (by positivity : 0 < 4 * log (log x))).mpr
    nlinarith
  rw [Real.log_div hx0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- The same gap is strict throughout the upper half of the counting interval. -/
theorem upper_half_product_gap {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      product (cutoff (log (log x))) * exp (C * (cutoff (log (log x))) ^ (-a)) <
        exp eulerMascheroniConstant * log (log (x / 2)) := by
  filter_upwards [(tendsto_log_atTop.comp tendsto_log_atTop).eventually (product_power_gap ha C),
    lower_half_loglog] with x hx hhalf
  exact hx.trans_lt (mul_lt_mul_of_pos_left hhalf (exp_pos _))

end D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap
