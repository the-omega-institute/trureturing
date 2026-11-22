/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMiddleGapMoments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational alternating Taylor bounds for the exponential moments. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterCollisionRadicand
import Mathlib.Analysis.Calculus.Taylor

/-! # Enclosing the exponential moments on a compact gap rectangle -/

open Set MeasureTheory intervalIntegral

namespace RefinedBMV.PositiveCenter

noncomputable def expNegPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-x) ^ k / (k.factorial : ℝ)

/-- The sign of the remainder is the sign of the next coefficient. -/
theorem expNegPartial_remainder_signed (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (-1 : ℝ) ^ (n + 1) * (Real.exp (-x) - expNegPartial n x) := by
  let f : ℝ → ℝ := fun t ↦ Real.exp ((-x) * t)
  have hDiff : ContDiff ℝ (n + 1 : ℕ) f := by dsimp only [f]; fun_prop
  have huniq : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc zero_ne_one
  have hpoly : taylorWithinEval f n (uIcc (0 : ℝ) 1) 0 1 = expNegPartial n x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    have h : ContDiffAt ℝ (k : ℕ) f 0 := by dsimp only [f]; fun_prop
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq h left_mem_uIcc]
    dsimp only [f]
    rw [iteratedDeriv_exp_const_mul]
    simp [div_eq_mul_inv, mul_comm]
  obtain ⟨s, _, hs⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := n) (f := f) (x₀ := 0) (x := 1) zero_ne_one hDiff.contDiffOn
  rw [hpoly] at hs
  have hs' : Real.exp (-x) - expNegPartial n x =
      (-x) ^ (n + 1) * Real.exp ((-x) * s) / ((n + 1).factorial : ℝ) := by
    unfold f at hs
    rw [iteratedDeriv_exp_const_mul] at hs
    simpa only [mul_one, sub_zero, one_pow] using hs
  have hm : (-1 : ℝ) ^ (n + 1) * (-x) ^ (n + 1) = x ^ (n + 1) := by
    rw [← mul_pow]
    simp
  rw [hs', ← mul_div_assoc, ← mul_assoc, hm]
  positivity

noncomputable def unitDecayMoment (j : ℕ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, s ^ j * Real.exp (-(x * s))

noncomputable def unitDecayMomentPartial (n j : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-x) ^ k / ((k.factorial : ℝ) * ((k + j : ℕ) + 1))

/-- Integrating the exponential bracket preserves the two signs. -/
theorem unitDecayMomentPartial_remainder_signed (n j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (-1 : ℝ) ^ (n + 1) * (unitDecayMoment j x - unitDecayMomentPartial n j x) := by
  let polynomial : ℝ → ℝ := fun s ↦ s ^ j * expNegPartial n (x * s)
  let actual : ℝ → ℝ := fun s ↦ s ^ j * Real.exp (-(x * s))
  let sign := (-1 : ℝ) ^ (n + 1)
  have hep : (∫ s in (0 : ℝ)..1, polynomial s) = unitDecayMomentPartial n j x := by
    unfold polynomial expNegPartial unitDecayMomentPartial
    simp only [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k _
      have he (s : ℝ) : s ^ j * (-(x * s)) ^ k / (k.factorial : ℝ) =
          ((-x) ^ k / (k.factorial : ℝ)) * s ^ (k + j) := by
        rw [← neg_mul, mul_pow, pow_add]
        ring
      simp_rw [← mul_div_assoc, he]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · intro k _
      apply Continuous.intervalIntegrable
      fun_prop
  have hp : IntervalIntegrable polynomial volume 0 1 := by
    unfold polynomial expNegPartial
    apply Continuous.intervalIntegrable
    fun_prop
  have hf : IntervalIntegrable actual volume 0 1 := by
    unfold actual
    apply Continuous.intervalIntegrable
    fun_prop
  change 0 ≤ sign * ((∫ s in (0 : ℝ)..1, actual s) - unitDecayMomentPartial n j x)
  rw [← hep, ← intervalIntegral.integral_sub hf hp, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro s hs
  have ht := expNegPartial_remainder_signed n (mul_nonneg hx hs.1)
  change 0 ≤ sign * (actual s - polynomial s)
  unfold actual polynomial
  nlinarith only [mul_nonneg (pow_nonneg hs.1 j) ht]

/-- The unit decay moments decrease with their nonnegative argument. -/
theorem unitDecayMoment_antitone (j : ℕ) : Antitone (unitDecayMoment j) := by
  intro x y hxy
  unfold unitDecayMoment
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop
  · intro s hs
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_right hxy hs.1))) (pow_nonneg hs.1 _)

/-- The physical moments, before scaling the gap to a unit interval. -/
noncomputable def gapDecayMoment (j : ℕ) (h d : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..d, s ^ j * Real.exp (-(h * s))

theorem gapDecayMoment_eq_scaled (j : ℕ) (h d : ℝ) :
    gapDecayMoment j h d = d ^ (j + 1) * unitDecayMoment j (h * d) := by
  unfold gapDecayMoment unitDecayMoment
  have ha : (∫ s in (0 : ℝ)..d, s ^ j * Real.exp (-(h * s))) =
      d * ∫ s in (0 : ℝ)..1, (d * s) ^ j * Real.exp (-(h * (d * s))) := by
    simpa only [mul_zero, mul_one, smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
        (fun s : ℝ ↦ s ^ j * Real.exp (-(h * s))) d).symm
  have hb : (∫ s in (0 : ℝ)..1, (d * s) ^ j * Real.exp (-(h * (d * s)))) =
      d ^ j * ∫ s in (0 : ℝ)..1, s ^ j * Real.exp (-(h * d * s)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [mul_pow, mul_assoc, mul_assoc h]
  rw [ha, hb, pow_succ]
  ring

theorem gapDecayMoment_antitone_rate (j : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    Antitone (fun h ↦ gapDecayMoment j h d) := by
  intro x y hxy
  change gapDecayMoment j y d ≤ gapDecayMoment j x d
  rw [gapDecayMoment_eq_scaled, gapDecayMoment_eq_scaled]
  exact mul_le_mul_of_nonneg_left ((unitDecayMoment_antitone j)
    (mul_le_mul_of_nonneg_right hxy hd)) (pow_nonneg hd _)

theorem gapDecayMoment_monotone_gap (j : ℕ) (h : ℝ) :
    MonotoneOn (gapDecayMoment j h) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  apply intervalIntegral.integral_mono_interval le_rfl ha hab
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (pow_nonneg hs.1.le j) (Real.exp_pos _).le
  · exact (by fun_prop : Continuous fun s : ℝ ↦ s ^ j * Real.exp (-(h * s))).intervalIntegrable _ _

theorem gapDecayMoment_zero_eq {h : ℝ} (hh : 0 < h) (d : ℝ) :
    gapDecayMoment 0 h d = upperTailGap h d := by
  rw [gapDecayMoment_eq_scaled]
  unfold unitDecayMoment
  simp only [Nat.zero_add, pow_zero, one_mul, pow_one]
  rw [expGapMean_eq hh]
  unfold expGapMean
  congr 1

theorem gapDecayMoment_succ_identity {h : ℝ} (d : ℝ) (j : ℕ) :
    h * gapDecayMoment (j + 1) h d =
      ((j : ℝ) + 1) * gapDecayMoment j h d - d ^ (j + 1) * Real.exp (-(h * d)) := by
  let f (s : ℝ) := s ^ (j + 1) * Real.exp (-(h * s))
  have hd (s : ℝ) : HasDerivAt f
      (((j : ℝ) + 1) * (s ^ j * Real.exp (-(h * s))) - h * f s) s := by
    have hs := hasDerivAt_id' s
    have he := ((hs.const_mul h).neg).exp
    refine ((hs.pow (j + 1)).fun_mul he).congr_deriv ?_
    simp only [f, Pi.pow_apply, Pi.neg_apply, Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one,
      mul_one, pow_succ]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    ((by dsimp only [f]; fun_prop : Continuous fun s : ℝ ↦
      ((j : ℝ) + 1) * (s ^ j * Real.exp (-(h * s))) - h * f s).intervalIntegrable 0 d)
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  · change ((j : ℝ) + 1) * gapDecayMoment j h d - h * gapDecayMoment (j + 1) h d =
      f d - f 0 at hint
    simp only [f, zero_pow (Nat.succ_ne_zero _), zero_mul, sub_zero] at hint
    linarith only [hint]
  all_goals apply Continuous.intervalIntegrable; (try dsimp only [f]); fun_prop

end RefinedBMV.PositiveCenter
