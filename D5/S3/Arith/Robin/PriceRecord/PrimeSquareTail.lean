/- GID: D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PrimeSquareTail
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Uniform prime reciprocal-square asymptotics and finite logarithmic refinements. -/

import D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
import D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity

/-! The lower endpoint is strict, including at prime integers. The leading
asymptotic allows any upper cutoff beyond a fixed multiple of the lower one.
The logarithmic refinements retain both finite endpoints for every z ≥ y.
All theta control is derived from the prime number theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail

open Finset Filter
open scoped Topology Chebyshev

/-- Lower Abel estimate retaining the finite upper-end correction. -/
private theorem finite_theta_abel_lower {y z rho : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (htheta : ∀ t ∈ Set.Icc y z,
      (1 - rho) * t ≤ θ t ∧ θ t ≤ (1 + rho) * t) :
    (1 - 3 * rho) / y - (1 - rho) / z ≤
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
        Real.log p / (p : ℝ) ^ 2 := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log p else 0
  let f : ℝ → ℝ := fun t => 1 / t ^ 2
  have hy0 : 0 < y := by linarith
  have hc (t : ℝ) : (∑ p ∈ Icc 0 ⌊t⌋₊, c p) = θ t := by
    simp only [c, ← sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hd (t : ℝ) (ht : t ∈ Set.Icc y z) : HasDerivAt f (-2 / t ^ 3) t := by
    have ht0 : t ≠ 0 := (hy0.trans_le ht.1).ne'
    convert (hasDerivAt_const t (1 : ℝ)).fun_div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 ht0) using 1 <;> dsimp [f]
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => -2 / t ^ 3) (Set.Icc y z) :=
    continuousOn_const.div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero _ (hy0.trans_le ht.1).ne')
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y z) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm)
      measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c hy0.le hyz
    (fun t ht => (hd t ht).differentiableAt) hi
  simp_rw [hc] at habel
  rw [← intervalIntegral.integral_of_le hyz] at habel
  have hprod : MeasureTheory.IntegrableOn (fun t => deriv f t * θ t) (Set.Icc y z) := by
    simpa only [hc] using integrableOn_mul_sum_Icc c hy0.le hi (m := 0)
  have hmajor : ContinuousOn (fun t : ℝ => -2 * (1 - rho) / t ^ 2)
      (Set.Icc y z) := continuousOn_const.div (continuousOn_id.pow 2)
        (fun t ht => pow_ne_zero _ (hy0.trans_le ht.1).ne')
  have hmajorint := hmajor.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hyz
  have hint := intervalIntegral.integral_mono_on hyz
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hyz).mpr hprod) hmajorint
    (fun t ht => by
      rw [(hd t ht).deriv]
      have ht0 : 0 < t := hy0.trans_le ht.1
      have hh := mul_le_mul_of_nonpos_left (htheta t ht).1
        (show -2 / t ^ 3 ≤ 0 by
          exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
      convert hh using 1
      field_simp)
  have hFTC : (∫ t in y..z, -2 * (1 - rho) / t ^ 2) =
      2 * (1 - rho) / z - 2 * (1 - rho) / y := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => 2 * (1 - rho) / t) _ hmajorint
    intro t ht
    rw [Set.uIcc_of_le hyz] at ht
    have ht0 : t ≠ 0 := (hy0.trans_le ht.1).ne'
    convert (hasDerivAt_const t (2 * (1 - rho))).fun_div (hasDerivAt_id t) ht0
      using 1 <;> simp only [id_eq, zero_mul, mul_one, zero_sub, neg_mul]
  rw [hFTC] at hint
  have htop : (1 - rho) / z ≤ f z * θ z := by
    have hh := mul_le_mul_of_nonneg_left (htheta z ⟨hyz, le_rfl⟩).1
      (show 0 ≤ f z by dsimp [f]; positivity)
    convert hh using 1
    dsimp [f]
    field_simp
  have hbot : f y * θ y ≤ (1 + rho) / y := by
    have hh := mul_le_mul_of_nonneg_left (htheta y ⟨le_rfl, hyz⟩).2
      (show 0 ≤ f y by dsimp [f]; positivity)
    convert hh using 1
    dsimp [f]
    field_simp
  have hs : (∑ p ∈ Ioc ⌊y⌋₊ ⌊z⌋₊, f p * c p) =
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
        Real.log p / (p : ℝ) ^ 2 := by
    simp only [sum_filter, c, f, mul_ite, mul_zero, one_div_mul_eq_div]
  rw [hs] at habel
  have heq : (1 - rho) / z - (1 + rho) / y -
      (2 * (1 - rho) / z - 2 * (1 - rho) / y) =
      (1 - 3 * rho) / y - (1 - rho) / z := by ring
  linarith

/-- Uniform in both real cutoffs, with a strict lower endpoint and no
additional error-control or record-integer premise. -/
theorem prime_square_tail_uniform (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 1 < C ∧ ∃ Y : ℝ, 1 < Y ∧
      ∀ y z : ℝ, Y ≤ y → C * y ≤ z →
        |y * Real.log y *
          (∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) ^ 2) - 1| < epsilon := by
  classical
  let eta : ℝ := min (epsilon / 16) (1 / 16)
  have heta0 : 0 < eta := lt_min (by positivity) (by norm_num)
  have heta16 : eta ≤ 1 / 16 := min_le_right _ _
  have hetaE : 16 * eta ≤ epsilon := by
    have h := min_le_left (epsilon / 16) (1 / 16 : ℝ)
    change eta ≤ epsilon / 16 at h
    linarith
  have heta1 : eta < 1 := by linarith
  let C : ℝ := 1 / eta
  have hC : 1 < C := (lt_div_iff₀ heta0).mpr (by linarith)
  have hC0 : 0 < C := by linarith
  have hCeta : C * eta = 1 := by dsimp [C]; field_simp
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (EulerLayerRootCorrection.prime_number_limits.2.eventually
      (Metric.ball_mem_nhds (1 : ℝ) heta0))
  let Y : ℝ := max T (max 2 (Real.exp (Real.log C / eta)))
  have hY : 1 < Y := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨C, hC, Y, hY, ?_⟩
  intro y z hYy hCz
  have hy : 1 < y := hY.trans_le hYy
  have hy0 : 0 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hyC : y ≤ C * y := by nlinarith
  have hyz : y ≤ z := hyC.trans hCz
  have htheta (t : ℝ) (hyt : y ≤ t) :
      (1 - eta) * t ≤ θ t ∧ θ t ≤ (1 + eta) * t := by
    have ht0 : 0 < t := hy0.trans_le hyt
    have hTt : T ≤ t := (le_max_left _ _).trans (hYy.trans hyt)
    have herr : |θ t / t - 1| < eta := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hT t hTt
    obtain ⟨hl, hu⟩ := abs_lt.mp herr
    constructor
    · exact (le_div_iff₀ ht0).mp (by linarith : 1 - eta ≤ θ t / t)
    · exact (div_le_iff₀ ht0).mp (by linarith : θ t / t ≤ 1 + eta)
  have hu := ActualPriceRecordPrimeStructure.finite_theta_abel_upper hy hyz heta0.le
    (fun t ht => htheta t ht.1)
  have hupper : y * Real.log y *
      (∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 + 3 * eta := by
    convert (le_div_iff₀ (mul_pos hy0 hlogy)).mp hu using 1 <;> ring
  have hlogCy : 0 < Real.log (C * y) := Real.log_pos (hy.trans_le hyC)
  have hlogbound : Real.log C ≤ eta * Real.log y := by
    have hexp : Real.exp (Real.log C / eta) ≤ y :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hYy)
    have h := (Real.log_le_log (Real.exp_pos _) hexp)
    rw [Real.log_exp] at h
    simpa only [mul_comm] using (div_le_iff₀ heta0).mp h
  have hlogratio : 1 - eta ≤ Real.log y / Real.log (C * y) := by
    apply (le_div_iff₀ hlogCy).mpr
    rw [Real.log_mul hC0.ne' hy0.ne']
    have hlogC : 0 ≤ Real.log C := (Real.log_pos hC).le
    nlinarith [mul_nonneg heta0.le hlogC, mul_nonneg heta0.le hlogy.le]
  have hweighted := finite_theta_abel_lower hy hyC
    (fun t ht => htheta t ht.1)
  have hcompare :
      (∑ p ∈ (Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime,
        Real.log p / (p : ℝ) ^ 2) ≤
      Real.log (C * y) *
        (∑ p ∈ (Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) ^ 2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpCy : (p : ℝ) ≤ C * y :=
      (Nat.cast_le.mpr (mem_Ioc.mp (mem_filter.mp hp).1).2).trans
        (Nat.floor_le (mul_pos hC0 hy0).le)
    have hlog := Real.log_le_log (by exact_mod_cast hpp.pos) hpCy
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr (sq_nonneg (p : ℝ)))
  have hfinite : (1 - 4 * eta) / y ≤
      Real.log (C * y) *
        (∑ p ∈ (Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) ^ 2) := by
    have hcorr : (1 - eta) / (C * y) ≤ eta / y := by
      apply (div_le_div_iff₀ (mul_pos hC0 hy0) hy0).mpr
      have hid : eta * (C * y) = y := by
        rw [← mul_assoc, mul_comm eta C, hCeta, one_mul]
      rw [hid]
      nlinarith [mul_pos heta0 hy0]
    calc
      (1 - 4 * eta) / y = (1 - 3 * eta) / y - eta / y := by ring
      _ ≤ (1 - 3 * eta) / y - (1 - eta) / (C * y) :=
        sub_le_sub_left hcorr _
      _ ≤ _ := hweighted.trans hcompare
  have hsub :
      (∑ p ∈ (Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ^ 2) ≤
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨(mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2.trans (Nat.floor_mono hCz)⟩, hpP⟩
    · intro p _ _
      positivity
  have hlower : 1 - 5 * eta ≤ y * Real.log y *
      (∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ^ 2) := by
    have hnonneg : 0 ≤ 1 - 4 * eta := by linarith
    have hr := mul_le_mul_of_nonneg_left hlogratio hnonneg
    have hf := mul_le_mul_of_nonneg_left hfinite
      (div_nonneg (mul_nonneg hy0.le hlogy.le) hlogCy.le)
    have heq : y * Real.log y / Real.log (C * y) * ((1 - 4 * eta) / y) =
        (1 - 4 * eta) * (Real.log y / Real.log (C * y)) := by field_simp [hy0.ne', hlogCy.ne']
    have heq' : y * Real.log y / Real.log (C * y) *
        (Real.log (C * y) *
          (∑ p ∈ (Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) ^ 2)) =
        y * Real.log y *
          (∑ p ∈ (Ioc ⌊y⌋₊ ⌊C * y⌋₊).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hlogCy.ne']
    rw [heq, heq'] at hf
    have hmono := mul_le_mul_of_nonneg_left hsub (mul_pos hy0 hlogy).le
    have hprod : 1 - 5 * eta ≤ (1 - 4 * eta) * (1 - eta) := by nlinarith [sq_nonneg eta]
    exact hprod.trans (hr.trans (hf.trans hmono))
  apply abs_lt.mpr
  constructor <;> linarith

private def logKernel (k : ℕ) (t : ℝ) : ℝ := 1 / (t ^ 2 * Real.log t ^ k)
private def logEndpoint (k : ℕ) (t : ℝ) : ℝ := 1 / (t * Real.log t ^ k)

private theorem logKernel_continuous {y z : ℝ} (hy : 1 < y) (k : ℕ) :
    ContinuousOn (logKernel k) (Set.Icc y z) := by
  apply continuousOn_const.div
    ((continuousOn_id.pow 2).mul ((Real.continuousOn_log.mono ?_).pow k))
  · intro t ht
    exact mul_ne_zero (pow_ne_zero _
      (show id t ≠ 0 from (lt_of_lt_of_le (by linarith : 0 < y) ht.1).ne'))
      (pow_ne_zero _ (Real.log_pos (hy.trans_le ht.1)).ne')
  · intro t ht
    exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) (hy.trans_le ht.1))

private theorem logEndpoint_deriv {t : ℝ} (ht : 1 < t) (k : ℕ) :
    HasDerivAt (logEndpoint k) (-logKernel k t - k * logKernel (k + 1) t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hL : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  convert (hasDerivAt_const t (1 : ℝ)).fun_div
    ((hasDerivAt_id t).mul ((Real.hasDerivAt_log ht0).pow k))
    (mul_ne_zero ht0 (pow_ne_zero _ hL)) using 1
  · rfl
  · dsimp [logKernel]
    cases k with
    | zero => simp <;> ring
    | succ k => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]; field_simp <;> ring

private theorem logKernel_integral_bounds {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (k : ℕ) :
    0 ≤ (∫ t in y..z, logKernel k t) ∧
      (∫ t in y..z, logKernel k t) ≤ logEndpoint k y := by
  have hy0 : 0 < y := by linarith
  have hLy : 0 < Real.log y := Real.log_pos hy
  have hkint := (logKernel_continuous hy k).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hyz
  let B : ℝ := 1 / Real.log y ^ k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hc : ContinuousOn (fun t : ℝ => B / t ^ 2) (Set.Icc y z) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (hy0.trans_le ht.1).ne')
  have hci := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hyz
  have hFTC : (∫ t in y..z, B / t ^ 2) = B / y - B / z := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => -B / t) (f' := fun t => B / t ^ 2) (a := y) (b := z)
      (fun t ht => by
        rw [Set.uIcc_of_le hyz] at ht
        convert (hasDerivAt_const t (-B)).fun_div (hasDerivAt_id t)
          (hy0.trans_le ht.1).ne' using 1 <;> simp <;> ring) hci
    simpa only [neg_div, neg_sub_neg] using h
  refine ⟨intervalIntegral.integral_nonneg hyz (fun t ht => by
    have ht0 : 0 < t := hy0.trans_le ht.1
    have hLt : 0 < Real.log t := Real.log_pos (hy.trans_le ht.1)
    dsimp [logKernel]; positivity), ?_⟩
  have hmono := intervalIntegral.integral_mono_on hyz hkint hci
    (fun t ht => by
      have ht0 : 0 < t := hy0.trans_le ht.1
      have hlog := Real.log_le_log hy0 ht.1
      have hp := pow_le_pow_left₀ hLy.le hlog k
      dsimp [logKernel, B]
      calc
        _ = (1 / Real.log t ^ k) / t ^ 2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (one_div_le_one_div_of_le (pow_pos hLy k) hp) (sq_nonneg t))
  rw [hFTC] at hmono
  have hBz : 0 ≤ B / z := div_nonneg hB (hy0.le.trans hyz)
  have heq : B / y = logEndpoint k y := by dsimp [B, logEndpoint]; ring
  linarith

private theorem logKernel_integral_step {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (k : ℕ) :
    (∫ t in y..z, logKernel k t) + k * (∫ t in y..z, logKernel (k + 1) t) =
      logEndpoint k y - logEndpoint k z := by
  have hi (n : ℕ) := (logKernel_continuous hy n).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hyz
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := logEndpoint k) (f' := fun t => -logKernel k t - k * logKernel (k + 1) t)
    (a := y) (b := z)
    (fun t ht => by
      rw [Set.uIcc_of_le hyz] at ht
      exact logEndpoint_deriv (hy.trans_le ht.1) k)
    ((hi k).neg.sub ((hi (k + 1)).const_mul (k : ℝ)))
  have heq := intervalIntegral.integral_sub (hi k).neg ((hi (k + 1)).const_mul (k : ℝ))
  change (∫ t in y..z, -logKernel k t - k * logKernel (k + 1) t) = _ at heq
  rw [heq] at h
  simp only [Pi.neg_apply, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at h
  linarith


private theorem finite_theta_abel_log_error {y z : ℝ} (hy : Real.exp 1 < y)
    (hyz : y ≤ z)
    (htheta : ∀ t ∈ Set.Icc y z, |θ t - t| ≤ t / Real.log t ^ 8) :
    |(∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) -
      (∫ t in y..z, logKernel 1 t)| ≤ 5 * logEndpoint 9 y := by
  classical
  have he1 : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hy1 : 1 < y := he1.trans hy
  have hy0 : 0 < y := by linarith
  have hLy : 1 ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos 1) hy.le
    simpa only [Real.log_exp] using h
  have hlog (t : ℝ) (ht : t ∈ Set.Icc y z) : 1 ≤ Real.log t :=
    hLy.trans (Real.log_le_log hy0 ht.1)
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log p else 0
  let f : ℝ → ℝ := logKernel 1
  let d : ℝ → ℝ := fun t => -2 / (t ^ 3 * Real.log t) -
    1 / (t ^ 3 * Real.log t ^ 2)
  have hc (t : ℝ) : (∑ p ∈ Icc 0 ⌊t⌋₊, c p) = θ t := by
    simp only [c, ← sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hd (t : ℝ) (ht : t ∈ Set.Icc y z) : HasDerivAt f (d t) t := by
    have ht0 : t ≠ 0 := (hy0.trans_le ht.1).ne'
    have hLt : Real.log t ≠ 0 := (Real.log_pos (hy1.trans_le ht.1)).ne'
    convert (hasDerivAt_const t (1 : ℝ)).fun_div
      (((hasDerivAt_id t).pow 2).mul (Real.hasDerivAt_log ht0))
      (mul_ne_zero (pow_ne_zero 2 ht0) hLt) using 1 <;>
      dsimp [f, d, logKernel]
    · funext u; simp [f, logKernel]
    · field_simp; ring
  have hdcont : ContinuousOn d (Set.Icc y z) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.div
        ((continuousOn_id.pow 3).mul (Real.continuousOn_log.mono
          (fun t ht => (hy0.trans_le ht.1).ne')))
        (fun t ht => mul_ne_zero (pow_ne_zero _ (hy0.trans_le ht.1).ne')
          (Real.log_pos (hy1.trans_le ht.1)).ne')
    · exact continuousOn_const.div
        ((continuousOn_id.pow 3).mul ((Real.continuousOn_log.mono
          (fun t ht => (hy0.trans_le ht.1).ne')).pow 2))
        (fun t ht => mul_ne_zero (pow_ne_zero _ (hy0.trans_le ht.1).ne')
          (pow_ne_zero _ (Real.log_pos (hy1.trans_le ht.1)).ne'))
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y z) :=
    hdcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm)
      measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c hy0.le hyz
    (fun t ht => (hd t ht).differentiableAt) hi
  simp_rw [hc] at habel
  rw [← intervalIntegral.integral_of_le hyz] at habel
  have hsum : (∑ p ∈ Ioc ⌊y⌋₊ ⌊z⌋₊, f p * c p) =
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases hpp : p.Prime
    · have hLp : Real.log (p : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
      simp only [c, hpp, ite_true, f, logKernel, pow_one]
      field_simp
    · simp [c, hpp]
  rw [hsum] at habel
  have hdtint : IntervalIntegrable (fun t => d t * t) MeasureTheory.volume y z := by
    exact ((hdcont.mul continuousOn_id).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hyz).congr
        (fun t _ => by simp only [Pi.mul_apply, id_eq])
  have hprod : IntervalIntegrable (fun t => deriv f t * θ t)
      MeasureTheory.volume y z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyz).mpr (by
      simpa only [hc] using integrableOn_mul_sum_Icc c hy0.le hi (m := 0))
  have hprod' : IntervalIntegrable (fun t => d t * θ t)
      MeasureTheory.volume y z := hprod.congr (fun t ht => by
        rw [Set.uIoc_of_le hyz] at ht
        rw [(hd t ⟨ht.1.le, ht.2⟩).deriv])
  have heqint : (∫ t in y..z, deriv f t * θ t) =
      (∫ t in y..z, d t * (θ t - t)) + (∫ t in y..z, d t * t) := by
    calc
      _ = ∫ t in y..z, d t * θ t := intervalIntegral.integral_congr
        (fun t ht => by rw [Set.uIcc_of_le hyz] at ht; rw [(hd t ht).deriv])
      _ = (∫ t in y..z, d t * θ t - d t * t) + (∫ t in y..z, d t * t) := by
        rw [intervalIntegral.integral_sub hprod' hdtint]; ring
      _ = _ := by
        have heq : (∫ t in y..z, d t * θ t - d t * t) =
            (∫ t in y..z, d t * (θ t - t)) :=
          intervalIntegral.integral_congr (fun t _ => by ring)
        rw [heq]
  have hmain : f z * z - f y * y - (∫ t in y..z, d t * t) =
      (∫ t in y..z, logKernel 1 t) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => f t * t) (f' := fun t => logKernel 1 t + d t * t)
      (a := y) (b := z)
      (fun t ht => by
        rw [Set.uIcc_of_le hyz] at ht
        convert (hd t ht).mul (hasDerivAt_id t) using 1
        · funext u; simp only [Pi.mul_apply, id_eq]
        · dsimp [f]; ring)
      (((logKernel_continuous hy1 1).intervalIntegrable_of_Icc
        (μ := MeasureTheory.volume) hyz).add hdtint)
    rw [intervalIntegral.integral_add
      ((logKernel_continuous hy1 1).intervalIntegrable_of_Icc
        (μ := MeasureTheory.volume) hyz) hdtint] at h
    linarith
  have hbound (t : ℝ) (ht : t ∈ Set.Icc y z) :
      |f t * (θ t - t)| ≤ logEndpoint 9 y ∧
      |d t * (θ t - t)| ≤ (3 / Real.log y ^ 9) / t ^ 2 := by
    have ht0 : 0 < t := hy0.trans_le ht.1
    have hLt : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (hlog t ht)
    have hLy0 : 0 < Real.log y := Real.log_pos hy1
    have hpow := pow_le_pow_left₀ hLy0.le (Real.log_le_log hy0 ht.1) 9
    have hmono : logEndpoint 9 t ≤ logEndpoint 9 y := by
      apply one_div_le_one_div_of_le (by positivity : 0 < y * Real.log y ^ 9)
      exact mul_le_mul ht.1 hpow (by positivity) ht0.le
    have hdneg : d t ≤ 0 := by
      dsimp [d]
      exact sub_nonpos.mpr ((div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)).trans
        (by positivity))
    have hfpos : 0 ≤ f t := by dsimp [f, logKernel]; positivity
    constructor
    · calc
        _ = f t * |θ t - t| := by rw [abs_mul, abs_of_nonneg hfpos]
        _ ≤ f t * (t / Real.log t ^ 8) := mul_le_mul_of_nonneg_left (htheta t ht) hfpos
        _ = logEndpoint 9 t := by dsimp [f, logKernel, logEndpoint]; field_simp <;> ring
        _ ≤ _ := hmono
    · have h10 : logKernel 10 t ≤ logKernel 9 t := by
        apply one_div_le_one_div_of_le (by positivity : 0 < t ^ 2 * Real.log t ^ 9)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hlog t ht) (by norm_num : 9 ≤ 10))
          (sq_nonneg t)
      have hk : logKernel 9 t ≤ (1 / Real.log y ^ 9) / t ^ 2 := by
        dsimp [logKernel]
        calc
          _ = (1 / Real.log t ^ 9) / t ^ 2 := by ring
          _ ≤ _ := div_le_div_of_nonneg_right
            (one_div_le_one_div_of_le (pow_pos hLy0 9) hpow) (sq_nonneg t)
      calc
        _ = (-d t) * |θ t - t| := by rw [abs_mul, abs_of_nonpos hdneg]
        _ ≤ (-d t) * (t / Real.log t ^ 8) :=
          mul_le_mul_of_nonneg_left (htheta t ht) (neg_nonneg.mpr hdneg)
        _ = 2 * logKernel 9 t + logKernel 10 t := by
          dsimp [d, logKernel]; field_simp <;> ring
        _ ≤ 3 * logKernel 9 t := by linarith
        _ ≤ 3 * ((1 / Real.log y ^ 9) / t ^ 2) := mul_le_mul_of_nonneg_left hk (by norm_num)
        _ = _ := by ring
  have hmajor : ContinuousOn
      (fun t : ℝ => (3 / Real.log y ^ 9) / t ^ 2) (Set.Icc y z) := by
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t (ht : t ∈ Set.Icc y z) => pow_ne_zero 2 (hy0.trans_le ht.1).ne')
  have hmajorint := hmajor.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hyz
  have herr := intervalIntegral.norm_integral_le_of_norm_le hyz
    (MeasureTheory.ae_of_all _ (fun t ht => by
      rw [Real.norm_eq_abs]; exact (hbound t ⟨ht.1.le, ht.2⟩).2)) hmajorint
  have hFTC : (∫ t in y..z, (3 / Real.log y ^ 9) / t ^ 2) =
      (3 / Real.log y ^ 9) / y - (3 / Real.log y ^ 9) / z := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => -(3 / Real.log y ^ 9) / t)
      (f' := fun t => (3 / Real.log y ^ 9) / t ^ 2) (a := y) (b := z)
      (fun t ht => by
        rw [Set.uIcc_of_le hyz] at ht
        convert (hasDerivAt_const t (-(3 / Real.log y ^ 9))).fun_div
          (hasDerivAt_id t) (hy0.trans_le ht.1).ne' using 1 <;> simp <;> ring) hmajorint
    simpa only [neg_div, neg_sub_neg] using h
  rw [hFTC, Real.norm_eq_abs] at herr
  have herr' : |∫ t in y..z, d t * (θ t - t)| ≤ 3 * logEndpoint 9 y := by
    have hn : 0 ≤ (3 / Real.log y ^ 9) / z := by
      have hz0 := hy0.trans_le hyz
      have hLy0 := Real.log_pos hy1
      positivity
    have heq : (3 / Real.log y ^ 9) / y = 3 * logEndpoint 9 y := by
      dsimp [logEndpoint]; ring
    linarith
  have heq : (∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) -
      (∫ t in y..z, logKernel 1 t) =
      f z * (θ z - z) - f y * (θ y - y) - (∫ t in y..z, d t * (θ t - t)) := by
    rw [habel, heqint, ← hmain]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add (hbound z ⟨hyz, le_rfl⟩).1
      (hbound y ⟨le_rfl, hyz⟩).1)) herr') |>.trans_eq (by ring)

/-- Uniform finite-endpoint second and third logarithmic refinements. The
single threshold is derived from PNT and precedes both real cutoffs. -/
theorem prime_square_tail_logarithmic_refinements :
    ∃ Y : ℝ, Real.exp 1 < Y ∧ ∀ y z : ℝ, Y ≤ y → y ≤ z →
      let S := ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2
      (|S -
          (1 / (y * Real.log y) - 1 / (y * Real.log y ^ 2)) +
          (1 / (z * Real.log z) - 1 / (z * Real.log z ^ 2))| ≤
        2 / (y * Real.log y ^ 3) + 5 / (y * Real.log y ^ 9)) ∧
      (|S -
          (1 / (y * Real.log y) - 1 / (y * Real.log y ^ 2) + 2 / (y * Real.log y ^ 3)) +
          (1 / (z * Real.log z) - 1 / (z * Real.log z ^ 2) + 2 / (z * Real.log z ^ 3))| ≤
        6 / (y * Real.log y ^ 4) + 5 / (y * Real.log y ^ 9)) := by
  have herror : ∀ᶠ t : ℝ in atTop, |θ t - t| ≤ t / Real.log t ^ 8 := by
    filter_upwards [LogarithmicLayerRigidity.theta_error_eight.eventuallyLE,
      eventually_gt_atTop (1 : ℝ)] with t ht ht1
    simpa only [Real.norm_eq_abs, abs_of_pos
      (div_pos (by linarith : 0 < t) (pow_pos (Real.log_pos ht1) 8))] using ht
  obtain ⟨T, hT⟩ := eventually_atTop.mp herror
  let Y := max T (Real.exp 1 + 1)
  have hY : Real.exp 1 < Y := lt_of_lt_of_le (by linarith)
    (le_max_right _ _)
  refine ⟨Y, hY, ?_⟩
  intro y z hYy hyz
  have hy : Real.exp 1 < y := hY.trans_le hYy
  have hy1 : 1 < y := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans hy
  have herr := finite_theta_abel_log_error hy hyz (fun t ht =>
    hT t ((le_max_left _ _).trans (hYy.trans ht.1)))
  let S : ℝ := ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2
  let I : ℕ → ℝ := fun k => ∫ t in y..z, logKernel k t
  have h1 := logKernel_integral_step hy1 hyz 1
  have h2 := logKernel_integral_step hy1 hyz 2
  have h3 := logKernel_integral_step hy1 hyz 3
  have hb3 := logKernel_integral_bounds hy1 hyz 3
  have hb4 := logKernel_integral_bounds hy1 hyz 4
  change |S - I 1| ≤ 5 * logEndpoint 9 y at herr
  change 0 ≤ I 3 ∧ I 3 ≤ logEndpoint 3 y at hb3
  change 0 ≤ I 4 ∧ I 4 ≤ logEndpoint 4 y at hb4
  norm_num at h1 h2 h3
  change I 1 + I 2 = logEndpoint 1 y - logEndpoint 1 z at h1
  change I 2 + (2 : ℝ) * I 3 = logEndpoint 2 y - logEndpoint 2 z at h2
  change I 3 + (3 : ℝ) * I 4 = logEndpoint 3 y - logEndpoint 3 z at h3
  have he2 : S - (logEndpoint 1 y - logEndpoint 2 y) +
      (logEndpoint 1 z - logEndpoint 2 z) = (S - I 1) + 2 * I 3 := by linarith
  have he3 : S - (logEndpoint 1 y - logEndpoint 2 y + 2 * logEndpoint 3 y) +
      (logEndpoint 1 z - logEndpoint 2 z + 2 * logEndpoint 3 z) =
      (S - I 1) - 6 * I 4 := by linarith
  have he2b : |(S - I 1) + 2 * I 3| ≤ 5 * logEndpoint 9 y + 2 * logEndpoint 3 y := by
    have h := abs_add_le (S - I 1) (2 * I 3)
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hb3.1)] at h
    exact h.trans (add_le_add herr (mul_le_mul_of_nonneg_left hb3.2 (by norm_num)))
  have he3b : |(S - I 1) - 6 * I 4| ≤ 5 * logEndpoint 9 y + 6 * logEndpoint 4 y := by
    have h := abs_sub (S - I 1) (6 * I 4)
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hb4.1)] at h
    exact h.trans (add_le_add herr (mul_le_mul_of_nonneg_left hb4.2 (by norm_num)))
  constructor
  · change |S - _ + _| ≤ _
    have h := he2b
    rw [← he2] at h
    dsimp [logEndpoint] at h
    simp only [pow_one] at h
    simpa only [mul_one_div, add_comm] using h
  · change |S - _ + _| ≤ _
    have h := he3b
    rw [← he3] at h
    dsimp [logEndpoint] at h
    simp only [pow_one] at h
    simpa only [mul_one_div, add_comm] using h

#print axioms prime_square_tail_logarithmic_refinements

end D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
