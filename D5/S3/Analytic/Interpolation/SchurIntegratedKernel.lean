/- GID: D5/S3/Analytic/Interpolation/SchurIntegratedKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SchurIntegratedKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Poisson, mathlib/module/Mathlib.MeasureTheory.Integral.Prod]
   utility: none
   digest: Integrated Poisson control for the actual Schur boundary kernel. -/

import D5.S3.Analytic.Interpolation.SchurBoundaryKernel
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Metric Complex MeasureTheory

namespace D5.S3.Analytic.Interpolation.SchurIntegratedKernel

open D5.S3.Analytic.Interpolation.SchurBoundaryKernel

/-- The original disk Poisson density, evaluated on the actual unit circle. -/
def poissonDensity (t θ : ℝ) : ℝ :=
  poissonKernel 0 (t : ℂ) (circleMap 0 1 θ)

/-- The original oriented integral of the Poisson densities. -/
def integratedPoisson (x θ : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, poissonDensity t θ

private theorem circle_norm (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  simpa using circleMap_mem_sphere' (0 : ℂ) (1 : ℝ) θ

private theorem density_continuousOn {r : ℝ} (hr : r < 1) :
    ContinuousOn (fun p : ℝ × ℝ => poissonDensity p.1 p.2)
      (Icc (-r) r ×ˢ (univ : Set ℝ)) := by
  unfold poissonDensity poissonKernel
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro p hp
    apply pow_ne_zero 2
    apply norm_ne_zero_iff.mpr
    simp only [sub_zero, sub_ne_zero]
    intro he
    have hh := congrArg norm he
    rw [circle_norm, Complex.norm_real, Real.norm_eq_abs] at hh
    have ht : |p.1| ≤ r := abs_le.mpr hp.1
    linarith

private theorem density_bounds {r t : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (ht : |t| ≤ r) (θ : ℝ) :
    (1 - |t|) / (1 + |t|) ≤ poissonDensity t θ ∧
      poissonDensity t θ ≤ (1 + r) / (1 - r) := by
  have hz : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := by
    simpa using circleMap_mem_sphere' (0 : ℂ) (1 : ℝ) θ
  have hw : (t : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using ht.trans_lt hr
  have hlo := le_re_herglotzRieszKernel hz hw
  have hup := re_herglotzRieszKernel_le hz hw
  rw [← herglotzRieszKernel_def, ← Function.comp_apply (f := Complex.re),
    ← poissonKernel_eq_re_herglotzRieszKernel] at hlo hup
  simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs] at hlo hup
  refine ⟨hlo, hup.trans ?_⟩
  apply (div_le_div_iff₀ (by linarith [abs_nonneg t]) (by linarith)).mpr
  nlinarith

private theorem density_angle_continuous {t : ℝ} (ht : |t| < 1) :
    Continuous (poissonDensity t) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hc := density_continuousOn (r := |t|) ht
  exact (hc (t, θ) ⟨abs_le.mp (le_refl |t|), mem_univ _⟩).comp_continuousAt
    (by fun_prop : ContinuousAt (fun φ : ℝ => (t, φ)) θ)
    (Filter.Eventually.of_forall (fun _ => ⟨abs_le.mp (le_refl |t|), mem_univ _⟩))

private theorem density_time_integrable {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (θ : ℝ) :
    IntervalIntegrable (fun t => poissonDensity t θ) volume (-r) r := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by linarith : -r ≤ r)] using
    (density_continuousOn hr).comp (by fun_prop : ContinuousOn (fun t : ℝ => (t, θ)) (Icc (-r) r))
      (fun t ht => ⟨ht, mem_univ θ⟩)

private theorem integrated_continuous {x : ℝ} (hx : |x| < 1) :
    Continuous (integratedPoisson x) := by
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun _ => (1 + |x|) / (1 - |x|))
  · intro θ
    exact ((density_time_integrable (abs_nonneg x) hx θ).mono_set
      (uIcc_subset_Icc (by constructor <;> linarith [abs_nonneg x])
        ⟨neg_abs_le x, le_abs_self x⟩)).aestronglyMeasurable
  · intro θ
    exact Filter.Eventually.of_forall (fun t ht => by
      have ht' : |t| ≤ |x| := by
        have h := uIoc_subset_uIcc ht
        have h' := uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-|x|) |x| by
          constructor <;> linarith [abs_nonneg x]) ⟨neg_abs_le x, le_abs_self x⟩ h
        exact abs_le.mpr h'
      have hh := density_bounds (abs_nonneg x) hx ht' θ
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        exact (div_nonneg (by linarith [ht'.trans_lt hx]) (by positivity)).trans hh.1)]
      exact hh.2)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t ht => by
      have hh := uIoc_subset_uIcc ht
      have hh' := uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-|x|) |x| by
        constructor <;> linarith [abs_nonneg x]) ⟨neg_abs_le x, le_abs_self x⟩ hh
      exact density_angle_continuous ((abs_le.mpr hh').trans_lt hx))

private def lowerPolynomial (t : ℝ) : ℝ :=
  ((1 - t) / 2) + ((1 - t) / 2) ^ 2 + ((1 - t) / 2) ^ 3 +
    ((1 - t) / 2) ^ 4 + ((1 - t) / 2) ^ 5

private theorem lowerPolynomial_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lowerPolynomial t ≤ (1 - t) / (1 + t) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 + t)).mpr
  have h := pow_nonneg (sub_nonneg.mpr ht.2) 6
  dsimp [lowerPolynomial]
  nlinarith [h]

private theorem lowerPolynomial_integral :
    (∫ t in (0 : ℝ)..1, lowerPolynomial t) = 367 / 960 := by
  have hp (n : ℕ) : (∫ t in (0 : ℝ)..1, ((1 - t) / 2) ^ n) =
      1 / ((n + 1 : ℕ) * (2 : ℝ) ^ n) := by
    have he : (fun t : ℝ => ((1 - t) / 2) ^ n) =
        (fun t => (1 - t) ^ n * (2 ^ n)⁻¹) := by
      funext t; simp [div_pow, div_eq_mul_inv]
    rw [he, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_sub_right (fun t : ℝ => t ^ n)]
    simp only [sub_self, sub_zero]
    rw [integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
    push_cast
    ring
  unfold lowerPolynomial
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simpa using (by norm_num [hp] :
      (∫ t in (0 : ℝ)..1, ((1 - t) / 2)) +
      (∫ t in (0 : ℝ)..1, ((1 - t) / 2) ^ 2) +
      (∫ t in (0 : ℝ)..1, ((1 - t) / 2) ^ 3) +
      (∫ t in (0 : ℝ)..1, ((1 - t) / 2) ^ 4) +
      (∫ t in (0 : ℝ)..1, ((1 - t) / 2) ^ 5) = 367 / 960)
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

private theorem integrated_lower_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    x * (3067 / 8100) ≤ integratedPoisson x θ := by
  by_cases hx : x = 0
  · simp [hx, integratedPoisson]
  have hchange : integratedPoisson x θ =
      x * ∫ t in (0 : ℝ)..1, poissonDensity (x * t) θ := by
    rw [intervalIntegral.integral_comp_mul_left _ hx]
    simp [integratedPoisson, smul_eq_mul, hx]
  have hlo : (367 / 960 : ℝ) ≤ ∫ t in (0 : ℝ)..1, poissonDensity (x * t) θ := by
    rw [← lowerPolynomial_integral]
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((show Continuous lowerPolynomial by unfold lowerPolynomial; fun_prop).intervalIntegrable _ _)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact (density_continuousOn hx1).comp (by fun_prop)
        (fun t ht => ⟨⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩, mem_univ θ⟩)
    · intro t ht
      have hxt : |x * t| ≤ x := by rw [abs_of_nonneg (mul_nonneg hx0 ht.1)]; nlinarith [ht.2]
      apply (lowerPolynomial_le ht).trans
      apply le_trans _ (density_bounds hx0 hx1 hxt θ).1
      rw [abs_of_nonneg (mul_nonneg hx0 ht.1)]
      apply (div_le_div_iff₀ (by positivity : 0 < 1 + t) (by positivity : 0 < 1 + x * t)).mpr
      nlinarith [ht.1, ht.2]
  rw [hchange]
  exact (mul_le_mul_of_nonneg_left (by norm_num : (3067 / 8100 : ℝ) ≤ 367 / 960) hx0).trans
    (mul_le_mul_of_nonneg_left hlo hx0)

end D5.S3.Analytic.Interpolation.SchurIntegratedKernel
