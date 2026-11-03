/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCoefficientIdentity
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitCoefficientIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reflection and coefficient identification for the actual finite slit. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCircleDefect
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCoefficientIdentity
open FiniteSlitCircleDefect

private theorem omega_im (z : ℂ) (hz : z.im ≠ 0) :
    z ∈ CompositionContinuation.omega := by
  change 1 - z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  right
  simpa using hz

private theorem reciprocal_conj (head : ℕ+) (tail : List ℕ+) (ell : ℕ+)
    (z : ℂ) (hz : z ∈ CompositionContinuation.omega) :
    FiniteSlitCompositionMoments.reciprocal head tail ell (conj z) =
      conj (FiniteSlitCompositionMoments.reciprocal head tail ell z) := by
  have hc := (CompositionSlit.result.2.2.1 head tail).2.2.2 z hz
  by_cases h0 : z = 0
  · subst z
    simp [FiniteSlitCompositionMoments.reciprocal,
      CompositionZeroFreeCollar.normalizedContinuation,
      (CompositionDisk.source_series head tail).2.1]
  · have hconj : conj z ≠ 0 := by simpa using h0
    simp only [FiniteSlitCompositionMoments.reciprocal,
      CompositionZeroFreeCollar.normalizedContinuation, if_neg h0, if_neg hconj,
      hc, map_pow, map_inv₀, map_div₀]

private theorem exp_circle (r y : ℝ) (hr : 0 < r) :
    Complex.exp ((Real.log r : ℂ) + y * I) = circleMap 0 r y := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr, circleMap_zero]

private theorem circle_pair (A P : ℂ → ℂ) (R r : ℝ) (n : ℕ)
    (hr : 0 < r) (hrR : r ≤ R)
    (hP : ContinuousOn P {z | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hPA : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega → P z = A z)
    (hconj : ∀ z ∈ CompositionContinuation.omega, A (conj z) = conj (A z))
    (hfi : CircleIntegrable (outerIntegrand A r n) 0 r) :
    (∮ z in C(0, r), outerIntegrand A r n z) =
      I * ((∫ y in (0 : ℝ)..Real.pi, upperPullback P n (Real.log r + y * I)) +
        conj (∫ y in (0 : ℝ)..Real.pi, upperPullback P n (Real.log r + y * I))) := by
  let q : ℝ → ℂ := fun y ↦ upperPullback P n (Real.log r + y * I)
  let f : ℝ → ℂ := fun y ↦ deriv (circleMap 0 r) y * outerIntegrand A r n (circleMap 0 r y)
  have hnorm (y : ℝ) : ‖circleMap 0 r y‖ = r := by
    rw [norm_circleMap_zero, abs_of_pos hr]
  have hq : ContinuousOn q (Icc 0 Real.pi) := by
    have heq : q = fun y ↦ P (circleMap 0 r y) / (circleMap 0 r y) ^ n := by
      funext y
      simp only [q, upperPullback, exp_circle r y hr]
    rw [heq]
    apply (hP.comp (continuous_circleMap 0 r).continuousOn ?_).div
      ((continuous_circleMap 0 r).continuousOn.pow n) ?_
    · intro y hy
      refine ⟨(hnorm y).le.trans hrR, ?_⟩
      rw [circleMap_zero_im]
      exact mul_nonneg hr.le (Real.sin_nonneg_of_mem_Icc hy)
    · intro y _
      exact pow_ne_zero _ (circleMap_ne_center hr.ne')
  have hupper (y : ℝ) (hy : y ∈ Ioo 0 Real.pi) : f y = I * q y := by
    have hi : 0 < (circleMap 0 r y).im := by
      rw [circleMap_zero_im]
      exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2)
    have ho := omega_im _ hi.ne'
    have hne : circleMap 0 r y ≠ (r : ℂ) := by
      intro h
      simpa [h] using hi
    have hz : circleMap 0 r y ≠ 0 := circleMap_ne_center hr.ne'
    dsimp [f, q]
    rw [upperPullback, exp_circle r y hr,
      hPA _ ((hnorm y).le.trans hrR) hi.le ho, outerIntegrand, if_neg hne]
    simp only [deriv_circleMap, sub_zero, smul_eq_mul]
    rw [pow_succ]
    field_simp
  have hlower (y : ℝ) (hy : y ∈ Ioo 0 Real.pi) : f (2 * Real.pi - y) = I * conj (q y) := by
    have hi : 0 < (circleMap 0 r y).im := by
      rw [circleMap_zero_im]
      exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2)
    have ho := omega_im _ hi.ne'
    have he : circleMap 0 r (2 * Real.pi - y) = conj (circleMap 0 r y) := by
      rw [conj_circleMap_zero, show 2 * Real.pi - y = -y + 2 * Real.pi by ring]
      exact periodic_circleMap 0 r (-y)
    have hne : conj (circleMap 0 r y) ≠ (r : ℂ) := by
      intro h
      have := congrArg Complex.im h
      simp only [conj_im, ofReal_im] at this
      linarith
    have hz : conj (circleMap 0 r y) ≠ 0 := by
      simpa using (circleMap_ne_center hr.ne' : circleMap 0 r y ≠ 0)
    dsimp [f, q]
    rw [upperPullback, exp_circle r y hr,
      hPA _ ((hnorm y).le.trans hrR) hi.le ho]
    simp only [deriv_circleMap, sub_zero, he, outerIntegrand, if_neg hne,
      hconj _ ho, map_div₀, map_pow]
    rw [pow_succ]
    field_simp
  have hfall : IntervalIntegrable f volume 0 (2 * Real.pi) := by
    simpa only [f, smul_eq_mul] using (circleIntegrable_iff r).mp hfi
  have hleft : IntervalIntegrable f volume 0 Real.pi := hfall.mono_set (by
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi), uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
  have hright : IntervalIntegrable f volume Real.pi (2 * Real.pi) := hfall.mono_set (by
    rw [uIcc_of_le (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi),
      uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact Icc_subset_Icc Real.pi_pos.le le_rfl)
  have hleftEq : (∫ y in (0 : ℝ)..Real.pi, f y) = I * ∫ y in (0 : ℝ)..Real.pi, q y := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le hupper
  have hrightEq : (∫ y in Real.pi..2 * Real.pi, f y) =
      I * conj (∫ y in (0 : ℝ)..Real.pi, q y) := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi) f (2 * Real.pi)
    simp only [sub_self, sub_zero, show 2 * Real.pi - Real.pi = Real.pi by ring] at hsub
    rw [← hsub, ← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le hlower
  change (∫ y in (0 : ℝ)..2 * Real.pi, f y) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hleftEq, hrightEq]
  ring

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCoefficientIdentity
