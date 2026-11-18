/- GID: D5/S3/Arith/Robin/Analytic/ExceptionCount/Mertens
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ExceptionCount/Mertens
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unconditional quantitative Mertens errors from the weighted Mangoldt rate. -/

import D5.S3.Weil.Mertens.WeightedMangoldtRate
import D5.S3.Weil.Mertens.Third
import D5.S3.Arith.Robin.LcmRobinResponse
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.ExceptionCount.Mertens

private theorem E2Lambda_stretched_exponential :
    ∃ c > 0, ∃ C > 0, ∃ X ≥ (2 : ℝ), ∀ x ≥ X,
      |_root_.Mertens.E₂Λ x| ≤
        C * exp (-c * (log x) ^ ((1 : ℝ) / 10)) / log x := by
  obtain ⟨c, hc, C, hC, X, hX, hbound⟩ :=
    D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential
  refine ⟨c, hc, 2 * C, by positivity, X, hX, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := hX.trans hx
  have hlx : 0 < log x := log_pos (by linarith)
  let H : ℝ → ℝ := fun u => _root_.Mertens.E₁Λ u + eulerMascheroniConstant
  let R : ℝ → ℝ := fun u => exp (-c * (log u) ^ ((1 : ℝ) / 10))
  have hint : IntegrableOn (fun u => H u / (u * log u ^ 2)) (Ioi x) := by
    have hi := (_root_.Mertens.integrable_E₁Λ_div_mul_log_sq hx2).add
      (_root_.Mertens.integrable_const_div_mul_log_sq eulerMascheroniConstant hx2)
    convert hi using 1
    ext u
    dsimp [H]
    ring
  have hid : _root_.Mertens.E₂Λ x =
      H x / log x - ∫ u in Ioi x, H u / (u * log u ^ 2) := by
    rw [_root_.Mertens.E₂Λ.eq hx2]
    have heq : (fun u => H u / (u * log u ^ 2)) =
        (fun u => _root_.Mertens.E₁Λ u / (u * log u ^ 2) +
          eulerMascheroniConstant / (u * log u ^ 2)) := by
      ext u; dsimp [H]; ring
    rw [heq, integral_add (_root_.Mertens.integrable_E₁Λ_div_mul_log_sq hx2)
      (_root_.Mertens.integrable_const_div_mul_log_sq eulerMascheroniConstant hx2),
      _root_.Mertens.integ_div_mul_log_sq _ hx2]
    dsimp [H]
    ring
  have hpoint (u : ℝ) (hu : u ∈ Ioi x) :
      |H u / (u * log u ^ 2)| ≤ (C * R x) / (u * log u ^ 2) := by
    have huX : X ≤ u := hx.trans hu.le
    have hu0 : 0 < u := by linarith [hu]
    have hlog : log x ≤ log u := log_le_log (by linarith) hu.le
    have hpow := Real.rpow_le_rpow hlx.le hlog (by norm_num : (0 : ℝ) ≤ 1 / 10)
    have hr : R u ≤ R x :=
      exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpow (by linarith : -c ≤ 0))
    rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ u * log u ^ 2)]
    exact div_le_div_of_nonneg_right ((hbound u huX).trans
      (mul_le_mul_of_nonneg_left hr hC.le)) (by positivity)
  have htail : |∫ u in Ioi x, H u / (u * log u ^ 2)| ≤ C * R x / log x := by
    calc
      _ ≤ ∫ u in Ioi x, |H u / (u * log u ^ 2)| := abs_integral_le_integral_abs
      _ ≤ ∫ u in Ioi x, (C * R x) / (u * log u ^ 2) :=
        setIntegral_mono_on hint.abs
          (_root_.Mertens.integrable_const_div_mul_log_sq _ hx2) measurableSet_Ioi hpoint
      _ = _ := _root_.Mertens.integ_div_mul_log_sq _ hx2
  rw [hid]
  calc
    _ ≤ |H x / log x| + |∫ u in Ioi x, H u / (u * log u ^ 2)| := abs_sub _ _
    _ ≤ C * R x / log x + C * R x / log x := by
      apply add_le_add _ htail
      rw [abs_div, abs_of_pos hlx]
      exact div_le_div_of_nonneg_right (hbound x hx) hlx.le
    _ = _ := by dsimp [R]; ring

private theorem prime_power_residual_bound {x : ℝ} (hx : 10000 ≤ x) :
    |D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.fullPrimePowerResidual x|
      ≤ 4 / sqrt x := by
  let S := D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.fullPrimePowerResidual
  have hx4 : 4 ≤ x := by linarith
  have hnonneg : 0 ≤ S x := by
    unfold S D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.fullPrimePowerResidual
    exact Finset.sum_nonneg (fun p hp => tsum_nonneg (fun k => by positivity))
  rw [abs_of_nonneg hnonneg]
  apply le_trans _ (D5.S3.Arith.Robin.LcmRobinResponse.lcm_tail_bound hx)
  unfold S D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.fullPrimePowerResidual
  rw [← Finset.sum_neg_distrib, Nat.primesLE_eq_filter_Ioc_zero]
  apply Finset.sum_le_sum
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hp1 : (1 : ℝ) < p := by linarith
  have hpx : (p : ℝ) ≤ x :=
    (Nat.le_floor_iff (by linarith : 0 ≤ x)).mp
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have hq0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hq1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  let b := D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.cutoffExponent x p
  have hspec := D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.cutoff_spec
    hx4 hpp hpx
  have hden : (1 : ℝ) ≤ (b + 1 : ℕ) * (1 - (p : ℝ)⁻¹) := by
    have hb : (2 : ℝ) ≤ (b + 1 : ℕ) := by exact_mod_cast (by dsimp [b]; omega : 2 ≤ b + 1)
    have hhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    nlinarith
  have hseries :=
    D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.shifted_tail_bound hq0 hq1 b
  rw [D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.residual_prime_eq_shift
    hx4 hpp hpx]
  have hpow : (p : ℝ)⁻¹ ^ (b + 1) =
      D5.S3.Arith.Robin.LcmRobinResponse.tailFactor x p := by
    dsimp [D5.S3.Arith.Robin.LcmRobinResponse.tailFactor]
    rw [show b = p.log ⌊x⌋₊ from hspec.2.2.2]
    simp only [one_div, inv_pow]
  calc
    _ ≤ ((p : ℝ)⁻¹ ^ (b + 1) / (b + 1 : ℕ)) / (1 - (p : ℝ)⁻¹) := hseries.2.le
    _ ≤ (p : ℝ)⁻¹ ^ (b + 1) := by
      rw [div_div]
      exact div_le_self (by positivity) hden
    _ = D5.S3.Arith.Robin.LcmRobinResponse.tailFactor x p := hpow
    _ ≤ -log (1 - D5.S3.Arith.Robin.LcmRobinResponse.tailFactor x p) := by
      let t := D5.S3.Arith.Robin.LcmRobinResponse.tailFactor x p
      have ht0 : 0 ≤ t := by dsimp [t, D5.S3.Arith.Robin.LcmRobinResponse.tailFactor]; positivity
      have ht1 : t < 1 := by
        dsimp [t]
        rw [← hpow]
        exact pow_lt_one₀ hq0.le hq1 (by omega)
      have hlog := log_le_sub_one_of_pos (by linarith : 0 < 1 - t)
      linarith

private theorem E3_stretched_exponential :
    ∃ c > 0, ∃ C > 0, ∀ᶠ x : ℝ in atTop,
      |_root_.Mertens.E₃ x| ≤ C * exp (-c * (log x) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, C, hC, X, hX, hbound⟩ := E2Lambda_stretched_exponential
  let b := min c (1 / 4)
  have hb : 0 < b := lt_min hc (by norm_num)
  have hbc : b ≤ c := min_le_left _ _
  have hbq : b ≤ 1 / 4 := min_le_right _ _
  refine ⟨b, hb, C + 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop X, eventually_ge_atTop (10000 : ℝ),
    eventually_ge_atTop (exp 1)] with x hx hxlarge hxe
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ log x := (le_log_iff_exp_le hx0).mpr hxe
  have hp0 : 0 ≤ (log x) ^ ((1 : ℝ) / 10) := rpow_nonneg (by linarith) _
  have hp : (log x) ^ ((1 : ℝ) / 10) ≤ log x :=
    rpow_le_self_of_one_le hlx (by norm_num)
  have hrate : exp (-c * (log x) ^ ((1 : ℝ) / 10)) ≤
      exp (-b * (log x) ^ ((1 : ℝ) / 10)) := by
    apply exp_le_exp.mpr
    nlinarith
  have hroot : 1 / sqrt x ≤ exp (-b * (log x) ^ ((1 : ℝ) / 10)) := by
    have he : 1 / sqrt x = exp (-log x / 2) := by
      rw [sqrt_eq_rpow, Real.rpow_def_of_pos hx0, one_div, ← exp_neg]
      congr 1
      ring
    rw [he]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hp hb.le]
  have hid :=
    D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.complete_mangoldt_add_E3_eq_neg_residual
      (show 4 ≤ x by linarith)
  calc
    |_root_.Mertens.E₃ x| =
        |-D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.fullPrimePowerResidual x -
          _root_.Mertens.E₂Λ x| := by congr 1; linarith only [hid]
    _ ≤ |D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.fullPrimePowerResidual x| +
        |_root_.Mertens.E₂Λ x| := by simpa only [abs_neg] using
          (abs_sub (-D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus.fullPrimePowerResidual x)
            (_root_.Mertens.E₂Λ x))
    _ ≤ 4 / sqrt x + C * exp (-c * (log x) ^ ((1 : ℝ) / 10)) / log x :=
      add_le_add (prime_power_residual_bound hxlarge) (hbound x hx)
    _ ≤ 4 * exp (-b * (log x) ^ ((1 : ℝ) / 10)) +
        C * exp (-b * (log x) ^ ((1 : ℝ) / 10)) := by
      apply add_le_add
      · simpa only [div_eq_mul_inv, one_div, one_mul] using
          mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 4)
      · exact (div_le_self (by positivity) hlx).trans
          (mul_le_mul_of_nonneg_left hrate hC.le)
    _ = _ := by ring

/-- The unconditional Mertens logarithmic error is smaller than the inverse
square logarithm. The prime-power residual and Euler normalization are exact. -/
theorem strengthened_mertens :
    (fun x : ℝ => _root_.Mertens.E₃ x) =o[atTop] (fun x : ℝ => 1 / (log x) ^ 2) := by
  obtain ⟨c, hc, C, hC, hbound⟩ := E3_stretched_exponential
  have hrate : Tendsto (fun x : ℝ =>
      log x ^ 2 * exp (-c * (log x) ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_log_atTop
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 20 c hc).comp ht
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp only [Function.comp_def]
    rw [← Real.rpow_mul (log_nonneg hx)]
    norm_num [Real.rpow_ofNat]
  apply isLittleO_of_tendsto' (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    intro hz
    have : 0 < 1 / (log x) ^ 2 := by have := log_pos hx; positivity
    exact (this.ne' hz).elim)
  apply squeeze_zero_norm' _ (by simpa using hrate.const_mul C)
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with x hx hxlarge
  have hlx : 0 < log x := log_pos hxlarge
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < 1 / log x ^ 2),
    div_div_eq_mul_div, div_one]
  calc
    _ ≤ (C * exp (-c * (log x) ^ ((1 : ℝ) / 10))) * log x ^ 2 :=
      mul_le_mul_of_nonneg_right hx (sq_nonneg _)
    _ = _ := by field_simp [hlx.ne']

end D5.S3.Arith.Robin.Analytic.ExceptionCount.Mertens
