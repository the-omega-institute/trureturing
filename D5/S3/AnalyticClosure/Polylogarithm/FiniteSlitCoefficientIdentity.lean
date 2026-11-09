/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCoefficientIdentity
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitCoefficientIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reflection and coefficient identification for the actual finite slit. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCircleDefect
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.TaylorSeries

/-! The radial jump and conjugate angular pairing for the same actual slit branch. -/

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

private theorem real_omega (x : ℝ) (hx : x < 1) :
    (x : ℂ) ∈ CompositionContinuation.omega := by
  change 1 - (x : ℂ) ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  left
  simpa using sub_pos.mpr hx

private theorem real_not_omega (x : ℝ) (hx : 1 ≤ x) :
    (x : ℂ) ∉ CompositionContinuation.omega := by
  change ¬ (1 - (x : ℂ) ∈ Complex.slitPlane)
  rw [Complex.mem_slitPlane_iff]
  simp only [sub_re, one_re, ofReal_re, sub_im, one_im, ofReal_im, sub_self, ne_eq,
    not_true_eq_false, or_false, not_lt]
  linarith

private theorem real_value (A : ℂ → ℂ)
    (hconj : ∀ z ∈ CompositionContinuation.omega, A (conj z) = conj (A z))
    (x : ℝ) (hx : x < 1) : (A (x : ℂ)).im = 0 := by
  have h := hconj (x : ℂ) (real_omega x hx)
  simp only [conj_ofReal] at h
  have h' := congrArg Complex.im h
  simp only [conj_im] at h'
  linarith

private theorem radial_im (A P upper : ℂ → ℂ) (R : ℝ) (n : ℕ)
    (hR : 1 < R)
    (hP : ContinuousOn P {z | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hPA : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega → P z = A z)
    (hPU : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∉ CompositionContinuation.omega → P z = upper z)
    (hconj : ∀ z ∈ CompositionContinuation.omega, A (conj z) = conj (A z)) :
    (∫ x in Real.log (1 / 2 : ℝ)..Real.log R, upperPullback P n (x : ℂ)).im =
      ∫ x in (1 : ℝ)..R, (upper (x : ℂ)).im / x ^ (n + 1) := by
  have hRpos : 0 < R := by linarith
  have hl : Real.log (1 / 2 : ℝ) ≤ Real.log R := Real.log_le_log (by norm_num) (by linarith)
  have hmap : MapsTo Real.exp (Icc (Real.log (1 / 2 : ℝ)) (Real.log R)) (Icc (1 / 2 : ℝ) R) := by
    intro x hx
    constructor
    · calc
        (1 / 2 : ℝ) = Real.exp (Real.log (1 / 2 : ℝ)) :=
          (Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)).symm
        _ ≤ Real.exp x := Real.exp_le_exp.mpr hx.1
    · simpa [Real.exp_log hRpos] using Real.exp_le_exp.mpr hx.2
  have hp : ContinuousOn (fun x : ℝ ↦ P (x : ℂ)) (Icc (1 / 2 : ℝ) R) := by
    apply hP.comp continuous_ofReal.continuousOn
    intro x hx
    refine ⟨?_, by simp⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
    exact hx.2
  let g : ℝ → ℝ := fun x ↦ (P (x : ℂ)).im / x ^ (n + 1)
  have hg : ContinuousOn g (Icc (1 / 2 : ℝ) R) :=
    (Complex.continuous_im.continuousOn.comp hp (fun _ _ ↦ mem_univ _)).div
      (continuousOn_id.pow (n + 1)) (fun x hx ↦ pow_ne_zero _ (by linarith [hx.1]))
  have hpb : ContinuousOn (fun x : ℝ ↦ P ((Real.exp x : ℝ) : ℂ) /
      (((Real.exp x : ℝ) : ℂ) ^ n)) (Icc (Real.log (1 / 2 : ℝ)) (Real.log R)) := by
    apply (hp.comp Real.continuous_exp.continuousOn hmap).div
      ((continuous_ofReal.comp Real.continuous_exp).continuousOn.pow n)
    intro x _
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x))
  have hbint : IntervalIntegrable (fun x : ℝ ↦ upperPullback P n (x : ℂ)) volume
      (Real.log (1 / 2 : ℝ)) (Real.log R) := by
    simpa only [upperPullback, ← Complex.ofReal_exp] using hpb.intervalIntegrable_of_Icc hl
  have hbim := Complex.imCLM.intervalIntegral_comp_comm hbint
  change (∫ x in Real.log (1 / 2 : ℝ)..Real.log R,
    (upperPullback P n (x : ℂ)).im) =
      (∫ x in Real.log (1 / 2 : ℝ)..Real.log R, upperPullback P n (x : ℂ)).im at hbim
  rw [← hbim]
  have hsub := intervalIntegral.integral_deriv_smul_comp'
    (a := Real.log (1 / 2 : ℝ)) (b := Real.log R)
    (f := Real.exp) (f' := Real.exp) (g := g)
    (fun x _ ↦ Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
    (hg.mono (by
      rw [Real.image_exp_uIcc, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2),
        Real.exp_log hRpos, uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ R)]))
  simp only [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2), Real.exp_log hRpos] at hsub
  have hbottom : (∫ x in Real.log (1 / 2 : ℝ)..Real.log R,
      (upperPullback P n (x : ℂ)).im) = ∫ x in (1 / 2 : ℝ)..R, g x := by
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [upperPullback, ← Complex.ofReal_exp, ← Complex.ofReal_pow,
      Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.normSq_ofReal, smul_eq_mul, Function.comp_apply, g, pow_succ]
    field_simp
    ring
  have hgi : IntervalIntegrable g volume (1 / 2 : ℝ) R :=
    hg.intervalIntegrable_of_Icc (by linarith : (1 / 2 : ℝ) ≤ R)
  have hgi1 : IntervalIntegrable g volume (1 / 2 : ℝ) 1 := hgi.mono_set (by
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
      uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ R)]
    exact Icc_subset_Icc le_rfl hR.le)
  have hgi2 : IntervalIntegrable g volume 1 R := hgi.mono_set (by
    rw [uIcc_of_le hR.le, uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ R)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  rw [hbottom, ← intervalIntegral.integral_add_adjacent_intervals hgi1 hgi2]
  have hz : (∫ x in (1 / 2 : ℝ)..1, g x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp [g]
    rw [hPA (x : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]) (by simp) (real_omega x hx.2), real_value A hconj x hx.2, zero_div]
  rw [hz, zero_add]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hR.le] at hx
  dsimp [g]
  rw [hPU (x : ℂ) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
    exact hx.2) (by simp) (real_not_omega x hx.1)]

private theorem top_im (A P : ℂ → ℂ) (R : ℝ) (n : ℕ) (hR : 1 < R)
    (hPA : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega → P z = A z)
    (hconj : ∀ z ∈ CompositionContinuation.omega, A (conj z) = conj (A z)) :
    (∫ x in Real.log (1 / 2 : ℝ)..Real.log R,
      upperPullback P n ((x : ℂ) + Real.pi * I)).im = 0 := by
  have hl : Real.log (1 / 2 : ℝ) ≤ Real.log R := Real.log_le_log (by norm_num) (by linarith)
  have he (x : ℝ) : Complex.exp ((x : ℂ) + Real.pi * I) = -(Real.exp x : ℂ) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
    ring
  have hre (x : ℝ) (hx : x ∈ Icc (Real.log (1 / 2 : ℝ)) (Real.log R)) :
      ‖(-(Real.exp x : ℂ))‖ ≤ R := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    simpa [Real.exp_log (show 0 < R by linarith)] using Real.exp_le_exp.mpr hx.2
  have hfix : (∫ x in Real.log (1 / 2 : ℝ)..Real.log R,
      conj (upperPullback P n ((x : ℂ) + Real.pi * I))) =
      ∫ x in Real.log (1 / 2 : ℝ)..Real.log R,
        upperPullback P n ((x : ℂ) + Real.pi * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hl] at hx
    have ho : (-(Real.exp x : ℂ)) ∈ CompositionContinuation.omega := by
      simpa using real_omega (-Real.exp x) (by linarith [Real.exp_pos x])
    simp only [upperPullback, he]
    rw [hPA _ (hre x hx) (by simp) ho]
    have hc := hconj _ ho
    have hc' : conj (A (-(Real.exp x : ℂ))) = A (-(Real.exp x : ℂ)) := by
      simpa only [map_neg, conj_ofReal] using hc.symm
    simp only [map_div₀, map_pow, map_neg, conj_ofReal, hc']
  rw [intervalIntegral.intervalIntegral_conj] at hfix
  have hi := congrArg Complex.im hfix
  simp only [conj_im] at hi
  linarith

private theorem inner_data (A : ℂ → ℂ) (R0 : ℝ) (hR0 : 1 < R0)
    (ha : AnalyticOnNhd ℂ A {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0})
    (n : ℕ) :
    CircleIntegrable (outerIntegrand A (1 / 2) n) 0 (1 / 2) ∧
    (∮ z in C(0, (1 / 2 : ℝ)), outerIntegrand A (1 / 2) n z) =
      (2 * Real.pi * I / (n.factorial : ℂ)) * iteratedDeriv n A 0 := by
  have hd : DifferentiableOn ℂ A (Metric.closedBall 0 (1 / 2 : ℝ)) := by
    intro z hz
    have hzn : ‖z‖ ≤ (1 / 2 : ℝ) := by simpa using hz
    have ho : z ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega, sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using (show ‖z‖ < 1 by linarith))
    exact (ha z ⟨ho, by linarith⟩).differentiableAt.differentiableWithinAt
  have hp : (fun z ↦ A z / z ^ (n + 1)) =ᶠ[
      codiscreteWithin (Metric.sphere (0 : ℂ) |(1 / 2 : ℝ)|)] outerIntegrand A (1 / 2) n := by
    filter_upwards [compl_singleton_mem_codiscreteWithin ((1 / 2 : ℝ) : ℂ)] with z hz
    have hne : z ≠ ((1 / 2 : ℝ) : ℂ) := hz
    simp only [outerIntegrand, if_neg hne]
  have hc : ContinuousOn (fun z ↦ A z / z ^ (n + 1)) (Metric.sphere 0 (1 / 2 : ℝ)) := by
    apply (hd.continuousOn.mono Metric.sphere_subset_closedBall).div
      (continuousOn_id.pow (n + 1))
    intro z hz
    apply pow_ne_zero
    intro hz0
    change z = 0 at hz0
    subst z
    norm_num [Metric.mem_sphere] at hz
  have hci : CircleIntegrable (fun z ↦ A z / z ^ (n + 1)) 0 (1 / 2 : ℝ) :=
    hc.circleIntegrable (by norm_num)
  refine ⟨CircleIntegrable.congr_codiscreteWithin hp hci, ?_⟩
  rw [← circleIntegral.circleIntegral_congr_codiscreteWithin hp (by norm_num)]
  simpa only [sub_zero, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul]
    using hd.circleIntegral_one_div_sub_center_pow_smul (by norm_num) n

private theorem normalized_pair (J : ℂ) :
    (2 * Real.pi * I : ℂ)⁻¹ * (I * (J + conj J)) =
      (((J.re / Real.pi : ℝ)) : ℂ) := by
  rw [RCLike.add_conj]
  change (2 * Real.pi * I : ℂ)⁻¹ * (I * (2 * (J.re : ℂ))) = _
  push_cast
  field_simp

private theorem coefficient_identity (A P upper : ℂ → ℂ) (R0 R : ℝ)
    (hR0 : 1 < R0) (hR : 1 < R)
    (ha : AnalyticOnNhd ℂ A {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0})
    (hP : ContinuousOn P {z | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hPA : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega → P z = A z)
    (hPU : ∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∉ CompositionContinuation.omega → P z = upper z)
    (hconj : ∀ z ∈ CompositionContinuation.omega, A (conj z) = conj (A z))
    (n : ℕ) (hfi : CircleIntegrable (outerIntegrand A R n) 0 R)
    (hrect : upperRectangleBalance P R n) :
    (iteratedDeriv n A 0 / (n.factorial : ℂ) = outerCoefficient A R n +
      (((1 / Real.pi) * ∫ x in (1 : ℝ)..R,
        (upper (x : ℂ)).im / x ^ (n + 1) : ℝ) : ℂ)) ∧
      (iteratedDeriv n A 0 / (n.factorial : ℂ)).im = 0 := by
  let Ji := ∫ y in (0 : ℝ)..Real.pi,
    upperPullback P n (Real.log (1 / 2 : ℝ) + y * I)
  let Jo := ∫ y in (0 : ℝ)..Real.pi, upperPullback P n (Real.log R + y * I)
  have hi := inner_data A R0 hR0 ha n
  have hip := circle_pair A P R (1 / 2) n (by norm_num) (by linarith) hPA hconj hi.1
  have hop := circle_pair A P R R n (by linarith) le_rfl hPA hconj hfi
  have hin : iteratedDeriv n A 0 / (n.factorial : ℂ) = ((Ji.re / Real.pi : ℝ) : ℂ) := by
    calc
      iteratedDeriv n A 0 / (n.factorial : ℂ) =
          (2 * Real.pi * I : ℂ)⁻¹ *
            ((2 * Real.pi * I / (n.factorial : ℂ)) * iteratedDeriv n A 0) := by
              field_simp
      _ = _ := by rw [← hi.2, hip]; exact normalized_pair Ji
  have hout : outerCoefficient A R n = ((Jo.re / Real.pi : ℝ) : ℂ) := by
    rw [outerCoefficient, hop]
    exact normalized_pair Jo
  have hb := radial_im A P upper R n hR hP hPA hPU hconj
  have ht := top_im A P R n hR hPA hconj
  have hrectim := congrArg Complex.im hrect
  change (_ - _ + I * Jo - I * Ji).im = (0 : ℂ).im at hrectim
  simp only [sub_im, add_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add,
    zero_im, hb, ht, sub_zero] at hrectim
  refine ⟨?_, by rw [hin]; exact Complex.ofReal_im _⟩
  rw [hin, hout, ← Complex.ofReal_add]
  congr 1
  field_simp
  linarith

/-- The actual same-source finite-slit coefficient identity, with one uniform outer bound. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    ∃ R0 ρ R B : ℝ, ∃ upper : ℂ → ℂ,
      1 < R0 ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < R ∧ R < R0 ∧ R < 1 + ρ ∧ 0 ≤ B ∧
      AnalyticOnNhd ℂ (FiniteSlitCompositionMoments.reciprocal head tail ell)
        {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0} ∧
      (∀ z : ℂ, ‖z‖ < 1 → FiniteSlitCompositionMoments.reciprocal head tail ell z =
        ((CompositionDisk.normalized head tail z)⁻¹) ^ (ell : ℕ)) ∧
      FiniteSlitCompositionMoments.reciprocal head tail ell 0 =
        ((CompositionDisk.normalized head tail 0)⁻¹) ^ (ell : ℕ) ∧
      ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im} ∧
      (∀ z : ℂ, ‖z - 1‖ ≤ ρ → 0 ≤ z.im → z ∈ CompositionContinuation.omega →
        upper z = FiniteSlitCompositionMoments.reciprocal head tail ell z) ∧
      (∀ n : ℕ, CircleIntegrable
          (outerIntegrand (FiniteSlitCompositionMoments.reciprocal head tail ell) R n) 0 R ∧
        IntervalIntegrable (fun x : ℝ ↦ (upper (x : ℂ)).im / x ^ (n + 1)) volume 1 R ∧
        ‖outerCoefficient (FiniteSlitCompositionMoments.reciprocal head tail ell) R n‖ ≤ B / R ^ n ∧
        iteratedDeriv n (FiniteSlitCompositionMoments.reciprocal head tail ell) 0 /
          (n.factorial : ℂ) =
          outerCoefficient (FiniteSlitCompositionMoments.reciprocal head tail ell) R n +
            (((1 / Real.pi) * ∫ x in (1 : ℝ)..R,
              (upper (x : ℂ)).im / x ^ (n + 1) : ℝ) : ℂ) ∧
        (iteratedDeriv n (FiniteSlitCompositionMoments.reciprocal head tail ell) 0 /
          (n.factorial : ℂ)).im = 0) ∧
      (∀ z : ℂ, ‖z‖ < 1 → HasSum
        (fun n : ℕ ↦ (iteratedDeriv n
          (FiniteSlitCompositionMoments.reciprocal head tail ell) 0 /
            (n.factorial : ℂ)) * z ^ n)
        (FiniteSlitCompositionMoments.reciprocal head tail ell z)) ∧
      (∀ᶠ n : ℕ in atTop, B / R ^ n + (1 / Real.pi) *
        (∫ x in (1 : ℝ)..R, (upper (x : ℂ)).im / x ^ (n + 1)) < 0) := by
  obtain ⟨R0, ρ, R, B, upper, P, hR0, hρ, hρ1, hR, hRR0, hRρ,
    hB, ha, hdisk, hzero, hu, he, hP, hPA, hPU, _hb, hi, hrect, hnegative⟩ :=
      FiniteSlitCircleDefect.result head tail ell
  refine ⟨R0, ρ, R, B, upper, hR0, hρ, hρ1, hR, hRR0, hRρ,
    hB, ha, hdisk, hzero, hu, he, ?_, ?_, hnegative⟩
  · intro n
    exact ⟨(hi n).1, (hi n).2.1, (hi n).2.2,
      coefficient_identity _ _ _ _ _ hR0 hR ha hP hPA hPU
        (reciprocal_conj head tail ell) n (hi n).1 (hrect n)⟩
  · have hd : DifferentiableOn ℂ
        (FiniteSlitCompositionMoments.reciprocal head tail ell) (Metric.ball 0 1) := by
      intro z hz
      have hzn : ‖z‖ < 1 := by simpa using hz
      have ho : z ∈ CompositionContinuation.omega := by
        simpa [CompositionContinuation.omega, sub_eq_add_neg] using
          Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hzn)
      exact (ha z ⟨ho, hzn.trans hR0⟩).differentiableAt.differentiableWithinAt
    intro z hz
    simpa only [sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using Complex.hasSum_taylorSeries_on_ball hd (show z ∈ Metric.ball 0 1 by simpa using hz)

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCoefficientIdentity
