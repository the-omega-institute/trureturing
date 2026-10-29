/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionCoefficientContour
   generality: G
   mirror-B: none(waiver:private-implementation-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite logarithmic-rectangle coefficient integrals for the actual composition reciprocal. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.AnalyticClosure.Polylogarithm.CompositionFiniteSlit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionCoefficientContour

open CompositionReciprocalSeries
open private coefficient_circle from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionReciprocalSeries
open private logLift actual_boundary_patches log_lift_continuous log_lift_differentiable
  log_lift_agrees exp_im_nonneg exp_im_nonpos from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionFiniteSlit

private def logIntegrand (g : ℂ → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  g w * Complex.exp (-(n : ℂ) * w)

private theorem log_rect_identity {g : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn g (Icc a b ×ℂ Icc 0 (2 * Real.pi)))
    (hd : DifferentiableOn ℂ g (Ioo a b ×ℂ Ioo 0 (2 * Real.pi))) (n : ℕ) :
    I * (∫ θ : ℝ in 0..2 * Real.pi, logIntegrand g n (a + θ * I)) =
      I * (∫ θ : ℝ in 0..2 * Real.pi, logIntegrand g n (b + θ * I)) +
        (∫ x : ℝ in a..b, logIntegrand g n x) -
        (∫ x : ℝ in a..b, logIntegrand g n (x + 2 * Real.pi * I)) := by
  have hce : Continuous (fun w : ℂ ↦ Complex.exp (-(n : ℂ) * w)) := by fun_prop
  have hde : Differentiable ℂ (fun w : ℂ ↦ Complex.exp (-(n : ℂ) * w)) := by fun_prop
  have hcn := hc.mul hce.continuousOn
  have hdn := hd.mul hde.differentiableOn
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (logIntegrand g n) (⟨a, 0⟩ : ℂ) (⟨b, 2 * Real.pi⟩ : ℂ)
    (by change ContinuousOn (fun w ↦ g w * Complex.exp (-(n : ℂ) * w)) _
        simpa only [Pi.mul_apply, uIcc_of_le hab.le,
          uIcc_of_le (by positivity : 0 ≤ 2 * Real.pi)]
          using hcn)
    (by change DifferentiableOn ℂ (fun w ↦ g w * Complex.exp (-(n : ℂ) * w)) _
        simpa only [Pi.mul_apply, min_eq_left hab.le, max_eq_right hab.le,
      min_eq_left (by positivity : 0 ≤ 2 * Real.pi),
      max_eq_right (by positivity : 0 ≤ 2 * Real.pi)] using hdn)
  dsimp only at h
  simp only [ofReal_zero, zero_mul, add_zero, smul_eq_mul, ofReal_mul, ofReal_ofNat] at h
  linear_combination -h

private theorem exp_log_kernel (n : ℕ) (w : ℂ) :
    Complex.exp (-(n : ℂ) * w) = ((Complex.exp w) ^ n)⁻¹ := by
  rw [neg_mul, Complex.exp_neg, Complex.exp_nat_mul]

private theorem log_inner_circle {f g : ℂ → ℂ} (a : ℝ)
    (hag : ∀ θ : ℝ, θ ∈ Icc 0 (2 * Real.pi) →
      g (a + θ * I) = f (Complex.exp (a + θ * I))) (n : ℕ) :
    I * (∫ θ : ℝ in 0..2 * Real.pi, logIntegrand g n (a + θ * I)) =
      circleIntegral (fun z ↦ f z / z ^ (n + 1)) 0 (Real.exp a) := by
  rw [circleIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθ' : θ ∈ Icc 0 (2 * Real.pi) := by
    rw [uIcc_of_le (by positivity : 0 ≤ 2 * Real.pi)] at hθ
    exact hθ
  have hmap : Complex.exp ((a : ℂ) + θ * I) = circleMap 0 (Real.exp a) θ := by
    simp [circleMap, Complex.exp_add, Complex.ofReal_exp]
  have hz : circleMap 0 (Real.exp a) θ ≠ 0 :=
    circleMap_ne_center (Real.exp_pos a).ne'
  simp only [logIntegrand, hag θ hθ', exp_log_kernel, hmap, deriv_circleMap,
    smul_eq_mul, circleMap_sub_center, sub_zero]
  field_simp [hz]
  <;> ring

private theorem log_integrand_norm (g : ℂ → ℂ) (n : ℕ) (b θ : ℝ) :
    ‖logIntegrand g n (b + θ * I)‖ =
      ‖g (b + θ * I)‖ * Real.exp (-(n : ℝ) * b) := by
  simp [logIntegrand, norm_mul, Complex.norm_exp]

private theorem actual_log_contour (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    ∃ R : ℝ, ∃ F G : ℂ → ℂ,
      1 < R ∧ (F 1).im = 0 ∧
      (∀ x : ℝ, 1 ≤ x → x ≤ R → G x = conj (F x)) ∧
      (∀ x : ℝ, 1 < x → x ≤ R → (F x).im < 0) ∧
      ContinuousOn (logLift F G)
        (Icc (Real.log (1 / 2)) (Real.log R) ×ℂ Icc 0 (2 * Real.pi)) ∧
      (∀ x : ℝ, Real.log (1 / 2) ≤ x → x ≤ Real.log R →
        logLift F G x = F (Real.exp x)) ∧
      (∀ x : ℝ, Real.log (1 / 2) ≤ x → x ≤ Real.log R →
        logLift F G (x + 2 * Real.pi * I) = G (Real.exp x)) ∧
      (∀ x : ℝ, Real.log (1 / 2) ≤ x → x ≤ 0 →
        F (Real.exp x) = G (Real.exp x)) ∧
      ∀ n : ℕ, (ordinaryCoefficient head tail ell n : ℂ) = (2 * Real.pi * I : ℂ)⁻¹ *
        (I * (∫ θ : ℝ in 0..2 * Real.pi,
          logIntegrand (logLift F G) n (Real.log R + θ * I)) +
          (∫ x : ℝ in Real.log (1 / 2)..Real.log R,
            logIntegrand (logLift F G) n x) -
          (∫ x : ℝ in Real.log (1 / 2)..Real.log R,
            logIntegrand (logLift F G) n (x + 2 * Real.pi * I))) := by
  obtain ⟨R, R0, hR, hRR0, hf, F, G, hF, hG, hFag, hGag, hF1, hconj, hneg⟩ :=
    actual_boundary_patches head tail ell
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have ha : Real.log (1 / 2) < 0 := Real.log_neg hhalf (by norm_num)
  have hb : 0 < Real.log R := Real.log_pos hR
  have hab : Real.log (1 / 2) < Real.log R := ha.trans hb
  have heR : Real.exp (Real.log R) ≤ R := (Real.exp_log hRpos).le
  have hc := log_lift_continuous hab.le heR hF hG hFag hGag
  have hd := log_lift_differentiable heR hRR0 hf hFag hGag
    (a := Real.log (1 / 2))
  have hrealOmega : ∀ x : ℝ, x < 1 → (x : ℂ) ∈ CompositionContinuation.omega := by
    intro x hx
    change 1 - (x : ℂ) ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    left
    simpa only [sub_re, one_re, ofReal_re] using sub_pos.mpr hx
  refine ⟨R, F, G, hR, hF1, hconj, hneg, hc, ?_, ?_, ?_, ?_⟩
  · intro x _ _
    simp [logLift, Real.pi_pos.le, Complex.ofReal_exp]
  · intro x _ _
    have him : (x + 2 * Real.pi * I : ℂ).im = 2 * Real.pi := by simp
    have hperiod : Complex.exp (x + 2 * Real.pi * I) = (Real.exp x : ℂ) := by
      simp [Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.ofReal_exp]
    simp [logLift, him, show ¬ 2 * Real.pi ≤ Real.pi by linarith [Real.pi_pos], hperiod]
  · intro x _ hx
    by_cases hx0 : x = 0
    · subst x
      simp only [Real.exp_zero]
      rw [hconj 1 le_rfl hR.le]
      apply Complex.ext <;> simp [hF1]
    · have he : Real.exp x < 1 := Real.exp_lt_one_iff.mpr (lt_of_le_of_ne hx hx0)
      have hn : ‖(Real.exp x : ℂ)‖ ≤ R := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact he.le.trans hR.le
      exact (hFag _ hn (by simp) (hrealOmega _ he)).trans
        (hGag _ hn (by simp) (hrealOmega _ he)).symm
  · intro n
    have hinner : ∀ θ : ℝ, θ ∈ Icc 0 (2 * Real.pi) →
        logLift F G (Real.log (1 / 2) + θ * I) =
          reciprocal head tail ell (Complex.exp (Real.log (1 / 2) + θ * I)) := by
      intro θ hθ
      let w : ℂ := Real.log (1 / 2) + θ * I
      have hwim : w.im = θ := by
        simp only [w, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
          mul_one, mul_zero, add_zero, zero_add]
      have hnorm : ‖Complex.exp w‖ = 1 / 2 := by
        rw [Complex.norm_exp]
        have hwre : w.re = Real.log (1 / 2) := by
          simp only [w, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
            mul_zero, zero_mul, sub_zero, add_zero]
        rw [hwre, Real.exp_log hhalf]
      have homega : Complex.exp w ∈ CompositionContinuation.omega := by
        simpa [CompositionContinuation.omega, sub_eq_add_neg] using
          Complex.mem_slitPlane_of_norm_lt_one (z := -Complex.exp w)
            (by rw [norm_neg, hnorm]; norm_num)
      change logLift F G w = _
      by_cases hpi : w.im ≤ Real.pi
      · simp only [logLift, if_pos hpi]
        exact hFag _ (by rw [hnorm]; linarith) (exp_im_nonneg (by simpa [hwim] using hθ.1) hpi) homega
      · simp only [logLift, if_neg hpi]
        exact hGag _ (by rw [hnorm]; linarith)
          (exp_im_nonpos (not_le.mp hpi).le (by simpa [hwim] using hθ.2)) homega
    have hi := log_inner_circle (Real.log (1 / 2)) hinner n
    rw [Real.exp_log hhalf] at hi
    rw [coefficient_circle, ← hi, log_rect_identity hab hc hd]

end D5.S3.AnalyticClosure.Polylogarithm.CompositionCoefficientContour
