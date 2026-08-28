/- GID: D5/S3/Analytic/Characterizations/VisibleGaussianMass
   generality: G
   mirror-B: D5/B/S3/Analytic/Characterizations/VisibleGaussianMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The odd-double-factorial series equals its completed Gaussian mass. -/

import Mathlib

open MeasureTheory
open scoped BigOperators Interval

namespace D5.S3.Analytic.Characterizations.VisibleGaussianMass

private lemma beta_coefficient_recurrence (n : ℕ) :
    (2 * n + 3 : ℝ) * (∫ u : ℝ in 0..1, (1 - u ^ 2) ^ (n + 1)) =
      (2 * n + 2 : ℝ) * (∫ u : ℝ in 0..1, (1 - u ^ 2) ^ n) := by
  let F : ℝ → ℝ := fun u => u * (1 - u ^ 2) ^ (n + 1)
  let F' : ℝ → ℝ := fun u =>
    (1 - u ^ 2) ^ (n + 1) - 2 * (n + 1) * u ^ 2 * (1 - u ^ 2) ^ n
  have hderiv : ∀ u : ℝ, HasDerivAt F (F' u) u := by
    intro u
    have hbase : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * u) u := by
      have h := (hasDerivAt_pow 2 u).const_sub (1 : ℝ)
      simpa using h
    have hraw := (hasDerivAt_id u).mul (hbase.pow (n + 1))
    refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)).congr_deriv ?_
    · simp [F, id]
    · simp only [F', id_eq, one_mul, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel, Pi.pow_apply]
      ring
  have hfund : (∫ u : ℝ in 0..1, F' u) = F 1 - F 0 := by
    apply intervalIntegral.integral_deriv_eq_sub' F
    · funext u
      exact (hderiv u).deriv
    · intro u hu
      exact (hderiv u).differentiableAt
    · fun_prop
  have hzero : F 1 - F 0 = 0 := by simp [F]
  rw [hzero] at hfund
  dsimp [F'] at hfund
  rw [intervalIntegral.integral_sub] at hfund
  · have hfactor : (fun u : ℝ => 2 * (n + 1) * u ^ 2 * (1 - u ^ 2) ^ n) =
        fun u => (2 * (n + 1) : ℝ) * (u ^ 2 * (1 - u ^ 2) ^ n) := by
      funext u
      ring
    rw [hfactor, intervalIntegral.integral_const_mul] at hfund
    have hrewrite : (fun u : ℝ => u ^ 2 * (1 - u ^ 2) ^ n) =
        fun u => (1 - u ^ 2) ^ n - (1 - u ^ 2) ^ (n + 1) := by
      funext u
      rw [pow_succ]
      ring
    rw [hrewrite, intervalIntegral.integral_sub] at hfund
    · ring_nf at hfund ⊢
      linarith
    · exact ((continuous_const.sub (continuous_id.pow 2)).pow n).intervalIntegrable 0 1
    · exact ((continuous_const.sub (continuous_id.pow 2)).pow (n + 1)).intervalIntegrable 0 1
  · exact ((continuous_const.sub (continuous_id.pow 2)).pow (n + 1)).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous
      (fun u : ℝ => 2 * (n + 1) * u ^ 2 * (1 - u ^ 2) ^ n)).intervalIntegrable 0 1

private lemma beta_coefficient_eq (n : ℕ) :
    (∫ u : ℝ in 0..1, (1 - u ^ 2) ^ n) =
      (2 ^ n * n.factorial : ℝ) /
        (Nat.doubleFactorial (2 * n + 1) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hrec := beta_coefficient_recurrence n
      have hden : (2 * n + 3 : ℝ) ≠ 0 := by positivity
      rw [show (∫ u : ℝ in 0..1, (1 - u ^ 2) ^ (n + 1)) =
          (2 * n + 2 : ℝ) * (∫ u : ℝ in 0..1, (1 - u ^ 2) ^ n) /
            (2 * n + 3) by
        rw [eq_div_iff hden]
        simpa [mul_comm] using hrec]
      rw [ih]
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
        Nat.doubleFactorial_add_two]
      rw [pow_succ, Nat.factorial_succ]
      push_cast
      field_simp
      ring

private lemma double_factorial_series_hasSum_integral (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => x ^ n / (Nat.doubleFactorial (2 * n + 1) : ℝ))
      (∫ u : ℝ in 0..1, Real.exp ((x / 2) * (1 - u ^ 2))) := by
  let term : ℕ → ℝ → ℝ := fun n u =>
    ((x / 2) ^ n / (n.factorial : ℝ)) * (1 - u ^ 2) ^ n
  let bound : ℕ → ℝ → ℝ := fun n _u => (x / 2) ^ n / (n.factorial : ℝ)
  have hseries : HasSum (fun n => ∫ u : ℝ in 0..1, term n u)
      (∫ u : ℝ in 0..1, Real.exp ((x / 2) * (1 - u ^ 2))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence bound
    · intro n
      exact (by fun_prop : Continuous (term n)).aestronglyMeasurable
    · intro n
      filter_upwards with u hu
      have hu0 : 0 ≤ u := by simpa using hu.1.le
      have hu1 : u ≤ 1 := by simpa using hu.2
      have hbase0 : 0 ≤ 1 - u ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (by linarith : 0 ≤ 1 + u)]
      have hbase1 : 1 - u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
      have hcoef : 0 ≤ (x / 2) ^ n / (n.factorial : ℝ) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcoef (pow_nonneg hbase0 n))]
      have hpow : (1 - u ^ 2) ^ n ≤ 1 := pow_le_one₀ hbase0 hbase1
      simpa [bound] using mul_le_mul_of_nonneg_left hpow hcoef
    · filter_upwards with u hu
      dsimp [bound]
      exact (NormedSpace.expSeries_div_hasSum_exp (x / 2)).summable
    · have hsum : (∑' n : ℕ, (x / 2) ^ n / (n.factorial : ℝ)) =
          Real.exp (x / 2) := by
        simpa only [← Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp (x / 2)).tsum_eq
      simp_rw [bound, hsum]
      exact intervalIntegrable_const
    · filter_upwards with u hu
      have hexp := NormedSpace.expSeries_div_hasSum_exp ((x / 2) * (1 - u ^ 2))
      have htermEq : (fun n : ℕ =>
          (((x / 2) * (1 - u ^ 2)) ^ n / (n.factorial : ℝ))) =
          fun n => term n u := by
        funext n
        dsimp [term]
        rw [mul_pow]
        ring
      rw [htermEq] at hexp
      simpa only [← Real.exp_eq_exp_ℝ] using hexp
  have hintegralTerm : (fun n => ∫ u : ℝ in 0..1, term n u) =
      fun n => x ^ n / (Nat.doubleFactorial (2 * n + 1) : ℝ) := by
    funext n
    dsimp [term]
    rw [intervalIntegral.integral_const_mul, beta_coefficient_eq]
    have hfact : (n.factorial : ℝ) ≠ 0 := by positivity
    have hdouble : (Nat.doubleFactorial (2 * n + 1) : ℝ) ≠ 0 := by positivity
    have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    rw [div_pow]
    exact div_mul_cancel₀ _ htwo
  rwa [hintegralTerm] at hseries

/-- For positive `x`, the odd-double-factorial power series is the visible part
of the Gaussian integral at scale `sqrt x`. -/
theorem visible_gaussian_mass (x : ℝ) (hx : 0 < x) :
    (∑' n : ℕ, x ^ n / (Nat.doubleFactorial (2 * n + 1) : ℝ)) =
      Real.exp (x / 2) / Real.sqrt x *
        (∫ t : ℝ in 0..Real.sqrt x, Real.exp (-t ^ 2 / 2)) := by
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hsum := double_factorial_series_hasSum_integral x hx.le
  calc
    (∑' n : ℕ, x ^ n / (Nat.doubleFactorial (2 * n + 1) : ℝ)) =
        ∫ u : ℝ in 0..1, Real.exp ((x / 2) * (1 - u ^ 2)) := hsum.tsum_eq
    _ = Real.exp (x / 2) *
        (∫ u : ℝ in 0..1, Real.exp (-((Real.sqrt x * u) ^ 2) / 2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      change Real.exp ((x / 2) * (1 - u ^ 2)) =
        Real.exp (x / 2) * Real.exp (-((Real.sqrt x * u) ^ 2) / 2)
      rw [← Real.exp_add]
      congr 1
      rw [mul_pow, hsqrt_sq]
      ring
    _ = Real.exp (x / 2) / Real.sqrt x *
        (∫ t : ℝ in 0..Real.sqrt x, Real.exp (-t ^ 2 / 2)) := by
      have hsub := intervalIntegral.mul_integral_comp_mul_left
        (f := fun t : ℝ => Real.exp (-t ^ 2 / 2))
        (a := 0) (b := 1) (c := Real.sqrt x)
      have hsub' : Real.sqrt x *
          (∫ u : ℝ in 0..1, Real.exp (-((Real.sqrt x * u) ^ 2) / 2)) =
          ∫ t : ℝ in 0..Real.sqrt x, Real.exp (-t ^ 2 / 2) := by
        simpa using hsub
      rw [← hsub']
      field_simp [hsqrt.ne']

#print axioms visible_gaussian_mass

end D5.S3.Analytic.Characterizations.VisibleGaussianMass
