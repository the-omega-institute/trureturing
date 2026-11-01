/- GID: D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PrimeSquareTail
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Uniform prime reciprocal-square asymptotics with two unrestricted real cutoffs. -/

import D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure

/-! The lower endpoint is strict, including at prime integers. The upper
cutoff is arbitrary once it exceeds a sufficiently large fixed multiple of
the lower cutoff. All theta control is derived from the prime number theorem. -/

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

end D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
