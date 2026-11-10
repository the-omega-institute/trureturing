/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMoments
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Discrete fourth bounds control cumulative second and fourth moment sampling. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthSampling
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CellMomentBounds
import D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareUpper

/-! Cumulative moment sampling with an exact terminal-cell correction. -/

open Set MeasureTheory
open scoped BigOperators ENNReal
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open VarianceTransferDefs
noncomputable section
set_option autoImplicit false

private theorem fourth_integral_eq_norm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    (∫ x, |f x| ^ 4 ∂μ) = lpNorm f 4 μ ^ 4 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_ofNat]
  simpa only [one_div, Nat.cast_ofNat] using
    (Real.rpow_inv_natCast_pow (x := ∫ x, |f x| ^ 4 ∂μ)
      (integral_nonneg (fun x => pow_nonneg (abs_nonneg _) 4))
      (by norm_num : (4 : ℕ) ≠ 0)).symm

private theorem probability_sampling_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ) (hk : k = 2 ∨ k = 4)
    (f g : Ω → ℝ) (A e : ℝ) (hA : 1 ≤ A) (he : 0 ≤ e)
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ)
    (hgb : (∫ x, |g x| ^ 4 ∂μ) ≤ A)
    (hdb : (∫ x, |f x - g x| ^ 4 ∂μ) ≤ e ^ 4) :
    |(∫ x, f x ^ k ∂μ) - (∫ x, g x ^ k ∂μ)| ≤
      16 * (1 + A) * (e + e ^ k) := by
  let a := lpNorm g 4 μ
  have ha : 0 ≤ a := lpNorm_nonneg
  have ha4 : a ^ 4 ≤ A := by rwa [fourth_integral_eq_norm hg] at hgb
  have hd : lpNorm (f - g) 4 μ ≤ e := by
    have hd4 : lpNorm (f - g) 4 μ ^ 4 ≤ e ^ 4 := by
      rw [← fourth_integral_eq_norm (hf.sub hg)]
      exact hdb
    exact (pow_le_pow_iff_left₀ lpNorm_nonneg he (by norm_num : (4 : ℕ) ≠ 0)).mp hd4
  have hfn : lpNorm f 4 μ ≤ a + e :=
    (lpNorm_le_lpNorm_add_lpNorm_sub' hg (by norm_num)).trans (add_le_add le_rfl hd)
  have hfb : (∫ x, |f x| ^ 4 ∂μ) ≤ (a + e) ^ 4 := by
    rw [fourth_integral_eq_norm hf]
    exact pow_le_pow_left₀ lpNorm_nonneg hfn 4
  have hgb' : (∫ x, |g x| ^ 4 ∂μ) ≤ (a + e) ^ 4 := by
    rw [fourth_integral_eq_norm hg]
    exact pow_le_pow_left₀ ha (le_add_of_nonneg_right he) 4
  have hp := scalar_stability μ k f g ((a + e) ^ 4) e hk (by positivity)
    he hf hg hfb hgb' hdb
  have hr : ((a + e) ^ 4) ^ (((k : ℝ) - 1) / 4) = (a + e) ^ (k - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (add_nonneg ha he), ← Real.rpow_natCast]
    congr 1
    rcases hk with rfl | rfl <;> norm_num
  rw [hr] at hp
  have hak (j : ℕ) (hj : j ≤ 4) : a ^ j ≤ 1 + A := by
    by_cases ha1 : a ≤ 1
    · exact (pow_le_one₀ ha ha1).trans (by linarith)
    · exact (pow_le_pow_right₀ (le_of_not_ge ha1) hj).trans (by linarith)
  rcases hk with rfl | rfl
  · norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hp
    have hh := mul_le_mul_of_nonneg_left (add_le_add_right (hak 1 (by norm_num)) e)
      (show 0 ≤ 2 * e by positivity)
    have hrest : 0 ≤ (1 + A) * e := by positivity
    have hrest2 : e ^ 2 ≤ (1 + A) * e ^ 2 := le_mul_of_one_le_left (sq_nonneg e) (by linarith)
    exact hp.trans (by nlinarith only [hh, hrest, hrest2])
  · norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hp
    have hc := add_pow_le ha he 3
    norm_num only [Nat.reduceSub, Nat.reducePow] at hc
    have hsum : a ^ 3 + e ^ 3 ≤ (1 + A) + e ^ 3 :=
      add_le_add (hak 3 (by norm_num)) le_rfl
    have hh := mul_le_mul_of_nonneg_left
      (hc.trans (mul_le_mul_of_nonneg_left hsum (by norm_num)))
      (show 0 ≤ 4 * e by positivity)
    have hrest : e ^ 4 ≤ (1 + A) * e ^ 4 :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    exact hp.trans (by nlinarith only [hh, hrest])

private theorem prefix_probability (Y : ℝ) (hY : 2 ≤ Y) :
    IsProbabilityMeasure
      ((ENNReal.ofReal (Y - 1))⁻¹ • volume.restrict (Icc (1 : ℝ) Y)) := by
  constructor
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by linarith))
    ENNReal.ofReal_ne_top

private theorem prefix_integral (Y : ℝ) (hY : 2 ≤ Y) (f : ℝ → ℝ) :
    (∫ x, f x ∂((ENNReal.ofReal (Y - 1))⁻¹ •
      volume.restrict (Icc (1 : ℝ) Y))) = (∫ x in (1 : ℝ)..Y, f x) / (Y - 1) := by
  rw [integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ Y - 1)]
  rw [intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ Y),
    ← integral_Icc_eq_integral_Ioc]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem prefix_sampling_bound (k : ℕ) (hk : k = 2 ∨ k = 4)
    (Y Q A e : ℝ) (hY : 2 ≤ Y) (hQ : 0 < Q) (hA : 1 ≤ A) (he : 0 ≤ e)
    (f g : ℝ → ℝ) (hf : Measurable f)
    (hg : MemLp g 4 (volume.restrict (Icc (1 : ℝ) Y)))
    (hgb : (∫ x in (1 : ℝ)..Y, |g x| ^ 4) ≤ A * Y * Q ^ 4)
    (hpoint : ∀ x ∈ Icc (1 : ℝ) Y, |f x - g x| ≤ e * Q) :
    |(∫ x in (1 : ℝ)..Y, f x ^ k) - (∫ x in (1 : ℝ)..Y, g x ^ k)| ≤
      32 * (1 + A) * Y * Q ^ k * (e + e ^ k) := by
  let μ := (ENNReal.ofReal (Y - 1))⁻¹ • volume.restrict (Icc (1 : ℝ) Y)
  let : IsProbabilityMeasure μ := prefix_probability Y hY
  have hY1 : 0 < Y - 1 := by linarith
  have hfinite : (ENNReal.ofReal (Y - 1))⁻¹ ≠ ∞ := by
    simp only [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]
    linarith
  have hgm : MemLp (fun x => g x / Q) 4 μ :=
    by
      simpa only [div_eq_mul_inv] using (hg.mul_const Q⁻¹).smul_measure hfinite
  have hdm : MemLp (fun x => f x / Q - g x / Q) 4 μ := by
    apply MemLp.of_bound ((hf.div_const Q).aestronglyMeasurable.sub hgm.aestronglyMeasurable) e
    apply Measure.ae_smul_measure _
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, Pi.sub_apply, ← sub_div, abs_div, abs_of_pos hQ]
    exact (div_le_iff₀ hQ).2 (hpoint x hx)
  have hfm : MemLp (fun x => f x / Q) 4 μ := by
    convert hdm.add hgm using 1
    ext x
    simp
  have hgb' : (∫ x, |g x / Q| ^ 4 ∂μ) ≤ 2 * A := by
    dsimp only [μ]
    simp_rw [abs_div, abs_of_pos hQ, div_pow]
    rw [prefix_integral Y hY, intervalIntegral.integral_div, div_div]
    apply (div_le_iff₀ (mul_pos (pow_pos hQ 4) hY1)).2
    apply hgb.trans
    have hy : Y ≤ 2 * (Y - 1) := by linarith
    have hm := mul_le_mul_of_nonneg_left hy (mul_nonneg (by linarith : 0 ≤ A)
      (pow_nonneg hQ.le 4))
    nlinarith only [hm]
  have hdb : (∫ x, |f x / Q - g x / Q| ^ 4 ∂μ) ≤ e ^ 4 := by
    calc
      _ ≤ ∫ _x, e ^ 4 ∂μ := by
        apply integral_mono_ae
          (by simpa only [Real.norm_eq_abs] using hdm.integrable_norm_pow (by norm_num : 4 ≠ 0))
          (integrable_const _)
        apply Measure.ae_smul_measure _
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        apply pow_le_pow_left₀ (abs_nonneg _) _ 4
        rw [← sub_div, abs_div, abs_of_pos hQ]
        exact (div_le_iff₀ hQ).2 (hpoint x hx)
      _ = _ := by simp
  have hp := probability_sampling_bound μ k hk _ _ (2 * A) e (by linarith)
    he hfm hgm hgb' hdb
  have hscale :
      (∫ x, (f x / Q) ^ k ∂μ) - (∫ x, (g x / Q) ^ k ∂μ) =
      ((∫ x in (1 : ℝ)..Y, f x ^ k) - (∫ x in (1 : ℝ)..Y, g x ^ k)) /
        (Q ^ k * (Y - 1)) := by
    dsimp only [μ]
    simp_rw [div_pow]
    rw [prefix_integral Y hY, prefix_integral Y hY,
      intervalIntegral.integral_div, intervalIntegral.integral_div]
    field_simp [hQ.ne', hY1.ne']
  rw [hscale, abs_div, abs_of_pos (mul_pos (pow_pos hQ k) hY1)] at hp
  have hp' := (div_le_iff₀ (mul_pos (pow_pos hQ k) hY1)).mp hp
  have hc : 16 * (1 + 2 * A) ≤ 32 * (1 + A) := by linarith
  have hm : 16 * (1 + 2 * A) * (e + e ^ k) * (Q ^ k * (Y - 1)) ≤
      32 * (1 + A) * (e + e ^ k) * (Q ^ k * Y) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hc (by positivity)
    · exact mul_le_mul_of_nonneg_left (by linarith : Y - 1 ≤ Y) (by positivity)
    · positivity
    · positivity
  exact hp'.trans (hm.trans_eq (by ring))

private theorem small_terminal_bound (n K : ℕ) (hn : 2 ≤ n) (hn3 : n ≤ 3)
    (hK : 1 ≤ K) (hK3 : K ≤ 3) : |primeIncrement (K : ℝ) (n : ℝ)| ≤ 3 * (K : ℝ) := by
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have h2' : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h3' : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h5' : Real.log 5 ≤ 4 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
  rw [integer_increment]
  interval_cases n <;> interval_cases K <;>
    norm_num [S, points, Finset.sum_Ioc_succ_top,
      ArithmeticFunction.vonMangoldt_apply] <;>
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

private theorem sampling_log_bounds (Y : ℝ) (hY : 2 ≤ Y) :
    1 / 2 ≤ Real.log Y ∧ 2 * Real.log (4 * Y) + 2 ≤ 10 * Real.log Y := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlo : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
  refine ⟨h2.trans hlo, ?_⟩
  rw [Real.log_mul (by norm_num) (by linarith : Y ≠ 0),
    show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith only [h2, hlo]

private theorem terminal_increment_bound (Y v : ℝ) (hY : 2 ≤ Y)
    (hv : 1 ≤ v) (hvY : v ≤ Y) :
    |primeIncrement (⌊v⌋₊ : ℝ) (⌊Y⌋₊ : ℝ)| ≤ 8 * v * Real.log Y := by
  have hv0 : 0 ≤ v := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hhalf := (sampling_log_bounds Y hY).1
  by_cases hL : 1 ≤ Real.log Y
  · have hQ : 0 < Real.sqrt (v * Real.log Y) := Real.sqrt_pos.mpr (by positivity)
    have hn : ⌊Y⌋₊ ≤ ⌈2 * Y⌉₊ :=
      (Nat.floor_mono (by linarith : Y ≤ 2 * Y)).trans (Nat.floor_le_ceil _)
    have hp := (normalized_crude_bounds Y v 1 hY hL hv (by norm_num)
      (by simpa using hvY)).1 0 1 ⌊Y⌋₊ (by norm_num) (by norm_num)
      (by norm_num) le_rfl hn
    rw [real_length_cell v ⌊Y⌋₊ hv0, abs_div, abs_of_pos hQ] at hp
    have hh := (div_le_iff₀ hQ).mp hp
    apply hh.trans_eq
    norm_num only [show (4 : ℝ) * (1 + 1) = 8 by norm_num]
    rw [mul_assoc, Real.mul_self_sqrt (by positivity : 0 ≤ v * Real.log Y)]
    ring
  · have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := (sampling_log_bounds 2 (by norm_num)).1
    have h4 : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith only [h2]
    have hY4 : Y < 4 := by
      by_contra h
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (le_of_not_gt h)
      linarith only [hL, h4, hlog]
    have hn4 : ⌊Y⌋₊ < 4 := (Nat.floor_lt hY0).mpr (by exact_mod_cast hY4)
    have hK4 : ⌊v⌋₊ < 4 := (Nat.floor_lt hv0).mpr (by exact_mod_cast hvY.trans_lt hY4)
    have hs := small_terminal_bound ⌊Y⌋₊ ⌊v⌋₊
      (Nat.le_floor (by simpa using hY)) (by omega)
      (Nat.le_floor (by simpa using hv)) (by omega)
    calc
      _ ≤ 3 * (⌊v⌋₊ : ℝ) := hs
      _ ≤ 3 * v := mul_le_mul_of_nonneg_left (Nat.floor_le hv0) (by norm_num)
      _ ≤ 8 * v * Real.log Y := by
        have hm := mul_le_mul_of_nonneg_left hhalf hv0
        nlinarith only [hm, hv0]

theorem sampling_prefix_estimate (k : ℕ) (hk : k = 2 ∨ k = 4)
    (A Y v : ℝ) (hA : 1 ≤ A) (hY : 2 ≤ Y) (hv : 1 ≤ v) (hvY : v ≤ Y)
    (hbound : discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2) :
    |continuousPrimeMoment k Y v -
      (∫ x in (1 : ℝ)..Y, primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ) ^ k)| ≤
      32 * (1 + A) * Y * Real.sqrt (v * Real.log Y) ^ k *
        (10 * Real.sqrt (Real.log Y / v) + (10 * Real.sqrt (Real.log Y / v)) ^ k) := by
  have hv0 : 0 < v := by linarith
  have hL : 0 < Real.log Y := Real.log_pos (by linarith)
  have hQ : 0 < Real.sqrt (v * Real.log Y) := Real.sqrt_pos.mpr (mul_pos hv0 hL)
  have hs : Real.log Y / Real.sqrt (v * Real.log Y) = Real.sqrt (Real.log Y / v) := by
    rw [Real.sqrt_mul hv0.le, div_mul_eq_div_div, div_right_comm, Real.div_sqrt,
      ← Real.sqrt_div hL.le]
  have hQ4 : Real.sqrt (v * Real.log Y) ^ 4 = v ^ 2 * Real.log Y ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sq_sqrt (mul_nonneg hv0.le hL.le), mul_pow]
  unfold continuousPrimeMoment
  apply prefix_sampling_bound k hk Y (Real.sqrt (v * Real.log Y)) A
    (10 * Real.sqrt (Real.log Y / v)) hY hQ hA (by positivity)
    (primeIncrement v) (fun x => primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ))
  · change Measurable (fun x => chebyshevError (x + v) - chebyshevError x)
    exact (DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable.1.comp (measurable_id.add_const v)).sub DyadicMeanSquareUpper.discrepancy_locallyBoundedMeasurable.1
  · exact step_memLp Y v
  · rw [hQ4]
    exact (step_fourth_le_sum Y v (by linarith)).trans
      (by simpa only [mul_assoc] using hbound)
  · intro x hx
    calc
      _ ≤ 10 * Real.log Y :=
        (sampling_cumulative_pointwise Y v x hY hv hvY hx).trans (sampling_log_bounds Y hY).2
      _ = (10 * Real.sqrt (Real.log Y / v)) * Real.sqrt (v * Real.log Y) := by
        rw [← hs]
        field_simp [hQ.ne']

private theorem sampling_terminal_error (k : ℕ) (Y v : ℝ) (hY : 2 ≤ Y)
    (hv : 1 ≤ v) (hvY : v ≤ Y) :
    |(∫ x in (1 : ℝ)..Y, primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ) ^ k) -
      discretePrimeMoment k ⌊Y⌋₊ ⌊v⌋₊| ≤
      8 ^ k * (Real.sqrt (v * Real.log Y) ^ k) ^ 2 := by
  have hL : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hv0 : 0 ≤ v := by linarith
  have hi := floor_integral_identity (fun n => primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ) ^ k)
    Y (by linarith)
  have hcoef : |Y - (⌊Y⌋₊ : ℝ) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Nat.floor_le (by linarith : 0 ≤ Y), Nat.lt_floor_add_one Y]
  have hpower : (Real.sqrt (v * Real.log Y) ^ k) ^ 2 = (v * Real.log Y) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt (mul_nonneg hv0 hL)]
  change |(∫ x in (1 : ℝ)..Y, primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ) ^ k) -
    (∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ) ^ k)| ≤ _
  rw [hi, abs_mul, abs_pow]
  calc
    _ ≤ 1 * (8 * v * Real.log Y) ^ k :=
      mul_le_mul hcoef
        (pow_le_pow_left₀ (abs_nonneg _) (terminal_increment_bound Y v hY hv hvY) k)
        (by positivity) (by norm_num)
    _ = _ := by rw [hpower, mul_pow, mul_pow]; ring

private theorem sampling_envelope_algebra (k : ℕ) (hk : k = 2 ∨ k = 4) (A Y q s : ℝ)
    (hA : 1 ≤ A) (hY : 0 < Y) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    32 * (1 + A) * Y * q ^ k * (10 * s + (10 * s) ^ k) +
      8 ^ k * (q ^ k) ^ 2 ≤
    400000 * (1 + A) * Y * q ^ k * (s + s ^ k + q ^ k / Y) := by
  have h10 : (10 : ℝ) ^ k ≤ 10000 := by rcases hk with rfl | rfl <;> norm_num
  have h8 : (8 : ℝ) ^ k ≤ 4096 := by rcases hk with rfl | rfl <;> norm_num
  have ha : 10 * s + (10 * s) ^ k ≤ 10000 * (s + s ^ k) := by
    rw [mul_pow]
    have h1 := mul_le_mul_of_nonneg_right h10 (pow_nonneg hs k)
    have h2 := mul_le_mul_of_nonneg_right (by norm_num : (10 : ℝ) ≤ 10000) hs
    linarith only [h1, h2]
  have hb : 8 ^ k * (q ^ k) ^ 2 ≤ 4096 * (1 + A) * (q ^ k) ^ 2 := by
    calc
      _ ≤ 4096 * (q ^ k) ^ 2 := mul_le_mul_of_nonneg_right h8 (sq_nonneg _)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        linarith only [hA]
  have hm := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ 32 * (1 + A) * Y * q ^ k by positivity)
  let p := (1 + A) * Y * q ^ k * (s + s ^ k)
  let r := (1 + A) * (q ^ k) ^ 2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  calc
    _ ≤ 320000 * p + 4096 * r := by
      convert add_le_add hm hb using 1
      dsimp [p, r]
      ring
    _ ≤ 400000 * (p + r) := by linarith only [hp, hr]
    _ = _ := by
      dsimp [p, r]
      field_simp [hY.ne']

private theorem sampling_estimate (k : ℕ) (hk : k = 2 ∨ k = 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ A Y v : ℝ, 1 ≤ A → 2 ≤ Y → 1 ≤ v → v ≤ Y →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2 →
      |continuousPrimeMoment k Y v - discretePrimeMoment k ⌊Y⌋₊ ⌊v⌋₊| ≤
        C * (1 + A) * Y * Real.sqrt (v * Real.log Y) ^ k *
          (Real.sqrt (Real.log Y / v) + Real.sqrt (Real.log Y / v) ^ k +
            Real.sqrt (v * Real.log Y) ^ k / Y) := by
  refine ⟨400000, by norm_num, ?_⟩
  intro A Y v hA hY hv hvY hbound
  have hp := sampling_prefix_estimate k hk A Y v hA hY hv hvY hbound
  have hc := sampling_terminal_error k Y v hY hv hvY
  have ha := sampling_envelope_algebra k hk A Y (Real.sqrt (v * Real.log Y))
    (Real.sqrt (Real.log Y / v)) hA (by linarith) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact (abs_sub_le (continuousPrimeMoment k Y v)
    (∫ x in (1 : ℝ)..Y, primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ) ^ k)
    (discretePrimeMoment k ⌊Y⌋₊ ⌊v⌋₊)).trans ((add_le_add hp hc).trans ha)

/-- A discrete fourth bound controls cumulative second-moment sampling. -/
theorem sampling_second :
    ∃ C : ℝ, 0 < C ∧ ∀ A Y v : ℝ, 1 ≤ A → 2 ≤ Y → 1 ≤ v → v ≤ Y →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2 →
      |continuousPrimeMoment 2 Y v - discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊| ≤
        C * (1 + A) * Y * (v * Real.log Y) *
          (Real.sqrt (Real.log Y / v) + Real.log Y / v + (v * Real.log Y) / Y) := by
  obtain ⟨C, hC, h⟩ := sampling_estimate 2 (Or.inl rfl)
  refine ⟨C, hC, ?_⟩
  intro A Y v hA hY hv hvY hbound
  have hL : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hv0 : 0 ≤ v := by linarith
  simpa only [Real.sq_sqrt (mul_nonneg hv0 hL), Real.sq_sqrt (div_nonneg hL hv0)] using
    h A Y v hA hY hv hvY hbound

/-- A discrete fourth bound controls cumulative fourth-moment sampling. -/
theorem sampling_fourth :
    ∃ C : ℝ, 0 < C ∧ ∀ A Y v : ℝ, 1 ≤ A → 2 ≤ Y → 1 ≤ v → v ≤ Y →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2 →
      |continuousPrimeMoment 4 Y v - discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊| ≤
        C * (1 + A) * Y * (v * Real.log Y) ^ 2 *
          (Real.sqrt (Real.log Y / v) + (Real.log Y / v) ^ 2 + (v * Real.log Y) ^ 2 / Y) := by
  obtain ⟨C, hC, h⟩ := sampling_estimate 4 (Or.inr rfl)
  refine ⟨C, hC, ?_⟩
  intro A Y v hA hY hv hvY hbound
  have hL : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hv0 : 0 ≤ v := by linarith
  have hQ4 : Real.sqrt (v * Real.log Y) ^ 4 = (v * Real.log Y) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (mul_nonneg hv0 hL)]
  have hs4 : Real.sqrt (Real.log Y / v) ^ 4 = (Real.log Y / v) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (div_nonneg hL hv0)]
  simpa only [hQ4, hs4] using h A Y v hA hY hv hvY hbound

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
