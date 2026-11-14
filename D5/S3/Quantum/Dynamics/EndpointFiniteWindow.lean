/- GID: D5/S3/Quantum/Dynamics/EndpointFiniteWindow
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/EndpointFiniteWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-window endpoint transition estimates with the off-diagonal spectral mass retained. -/

import D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Matrix Finset Complex MeasureTheory
open scoped BigOperators

namespace D5.S3.Quantum.Dynamics.EndpointFiniteWindow

private def phase (x t : ℝ) : ℂ := Complex.exp (-Complex.I * (x : ℂ) * t)

private lemma phase_continuous (x : ℝ) : Continuous (phase x) := by
  unfold phase
  fun_prop

private lemma phase_norm (x t : ℝ) : ‖phase x t‖ = 1 := by
  have h : -Complex.I * (x : ℂ) * t = ((-x * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [phase, h, Complex.norm_exp_ofReal_mul_I]

private lemma phase_mul_star (x y t : ℝ) :
    phase x t * star (phase y t) = phase (x - y) t := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, map_neg,
    Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add, Complex.ofReal_sub]
  congr 1
  ring

private lemma phase_integral_bound {x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ |x|) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, phase x t‖ ≤ 2 / δ := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; linarith
  have hc : -Complex.I * (x : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hx0)
  have he : (∫ t in (0 : ℝ)..T, phase x t) =
      (phase x T - 1) / (-Complex.I * (x : ℂ)) := by
    simpa [phase, mul_assoc] using (integral_exp_mul_complex (a := 0) (b := T) hc)
  rw [he, norm_div]
  have hn : ‖-Complex.I * (x : ℂ)‖ = |x| := by simp [norm_mul]
  rw [hn]
  calc
    ‖phase x T - 1‖ / |x| ≤ 2 / |x| := by
      apply div_le_div_of_nonneg_right _ (abs_nonneg x)
      calc
        ‖phase x T - 1‖ ≤ ‖phase x T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [phase_norm]; norm_num
    _ ≤ 2 / δ := div_le_div_of_nonneg_left (by norm_num) hδ hx

private lemma probability_expansion {ι : Type*} [Fintype ι] (a λ : ι → ℝ) (t : ℝ) :
    Complex.normSq (∑ i, (a i : ℂ) * phase (λ i) t) =
      ∑ i, ∑ j, a i * a j * (phase (λ i - λ j) t).re := by
  have h := congrArg Complex.re
    (D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation.OpLidarTwinProbability.normSq_finite_sum
      (fun i => (a i : ℂ) * phase (λ i) t))
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [star_mul, star_ofReal]
  have he : (a i : ℂ) * phase (λ i) t * ((a j : ℂ) * star (phase (λ j) t)) =
      ((a i * a j : ℝ) : ℂ) * phase (λ i - λ j) t := by
    rw [Complex.ofReal_mul, ← phase_mul_star]
    ring
  rw [he, Complex.re_ofReal_mul]

/-- Averaging separated frequencies retains the exact off-diagonal coefficient mass. -/
theorem finite_window_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a λ w : ι → ℝ) (hw : ∀ i, |a i| = w i) (hsum : ∑ i, w i = 1)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    (hgap : ∀ i j, i ≠ j → δ ≤ |λ i - λ j|) :
    (∑ i, w i ^ 2) - (2 / (T * δ)) * (1 - ∑ i, w i ^ 2) ≤
      T⁻¹ * ∫ t in (0 : ℝ)..T, Complex.normSq (∑ i, (a i : ℂ) * phase (λ i) t) := by
  have hi (i j : ι) : IntervalIntegrable
      (fun t => a i * a j * (phase (λ i - λ j) t).re) volume 0 T :=
    (continuous_const.mul (phase_continuous _).re).intervalIntegrable _ _
  have he : (∫ t in (0 : ℝ)..T,
      Complex.normSq (∑ i, (a i : ℂ) * phase (λ i) t)) =
      ∑ i, ∑ j, a i * a j * (∫ t in (0 : ℝ)..T, phase (λ i - λ j) t).re := by
    simp_rw [probability_expansion]
    rw [intervalIntegral.integral_finsetSum (fun i _ =>
      IntervalIntegrable.sum (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_re (phase_continuous _).intervalIntegrable]
  have hdiag (i : ι) :
      a i * a i * (∫ t in (0 : ℝ)..T, phase (λ i - λ i) t).re = T * w i ^ 2 := by
    have hs : a i ^ 2 = w i ^ 2 := by rw [← hw, sq_abs]
    simp [phase, hs, ← pow_two, mul_comm]
  have hterm (i j : ι) (hij : i ≠ j) :
      -(2 / δ) * (w i * w j) ≤
        a i * a j * (∫ t in (0 : ℝ)..T, phase (λ i - λ j) t).re := by
    have hb := phase_integral_bound hδ (hgap i j hij) T
    have hr := Complex.abs_re_le_norm (∫ t in (0 : ℝ)..T, phase (λ i - λ j) t)
    have hh : |a i * a j * (∫ t in (0 : ℝ)..T, phase (λ i - λ j) t).re| ≤
        (w i * w j) * (2 / δ) := by
      rw [abs_mul, abs_mul, hw, hw]
      exact mul_le_mul_of_nonneg_left (hr.trans hb)
        (mul_nonneg (by rw [← hw]; positivity) (by rw [← hw]; positivity))
    linarith [neg_abs_le (a i * a j * (∫ t in (0 : ℝ)..T, phase (λ i - λ j) t).re)]
  have hmass : (∑ i, ∑ j ∈ univ.erase i, w i * w j) = 1 - ∑ i, w i ^ 2 := by
    have hrow (i : ι) : (∑ j ∈ univ.erase i, w i * w j) = w i - w i ^ 2 := by
      rw [Finset.sum_erase_eq_sub (mem_univ i), ← Finset.mul_sum, hsum]
      ring
    simp_rw [hrow]
    rw [Finset.sum_sub_distrib, hsum]
  have htotal : T * (∑ i, w i ^ 2) - (2 / δ) * (1 - ∑ i, w i ^ 2) ≤
      ∫ t in (0 : ℝ)..T, Complex.normSq (∑ i, (a i : ℂ) * phase (λ i) t) := by
    rw [he, ← hmass, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.add_sum_erase _ _ (mem_univ i), hdiag]
    have hh := Finset.sum_le_sum (fun j (hj : j ∈ univ.erase i) =>
      hterm i j (ne_of_mem_erase hj).symm)
    simp only [Finset.mul_sum] at *
    linarith
  have h := mul_le_mul_of_nonneg_left htotal (inv_pos.mpr hT).le
  convert h using 1 <;> field_simp <;> ring

end D5.S3.Quantum.Dynamics.EndpointFiniteWindow
