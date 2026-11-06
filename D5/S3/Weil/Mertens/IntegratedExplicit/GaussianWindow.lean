/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/GaussianWindow
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/GaussianWindow
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Complex Gaussian cancellation on the closed logarithmic window with both tails retained. -/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! The Gaussian has mean 2*w^2 and variance w^2/2. The lower-tail tilt
is valid even on the negative real axis; the window itself is closed.
All estimates are analytic families, not finite computations or certificates. -/

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace D5.S3.Weil.Mertens.IntegratedExplicit.GaussianWindow

private def variance (w : ℝ) : ℝ≥0 := NNReal.mk (w ^ 2 / 2) (by positivity)

def gaussian (w : ℝ) : Measure ℝ := gaussianReal (2 * w ^ 2) (variance w)

def frequency (a γ : ℝ) : ℂ := ⟨-a, γ⟩

instance gaussian_isProbabilityMeasure (w : ℝ) : IsProbabilityMeasure (gaussian w) := by
  unfold gaussian
  infer_instance

private lemma integrable_exp_linear (w t : ℝ) :
    Integrable (fun y : ℝ => exp (t * y)) (gaussian w) :=
  integrable_exp_mul_gaussianReal t

private lemma integral_exp_linear (w t : ℝ) :
    (∫ y : ℝ, exp (t * y) ∂gaussian w) =
      exp (2 * w ^ 2 * t + w ^ 2 * t ^ 2 / 4) := by
  have h := congrFun (mgf_fun_id_gaussianReal
    (μ := 2 * w ^ 2) (v := variance w)) t
  change (∫ y : ℝ, exp (t * y) ∂gaussian w) = _ at h
  rw [h]
  congr 1
  simp only [variance, NNReal.coe_mk]
  ring

private lemma integrable_cexp_linear (w : ℝ) (z : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (z * y)) (gaussian w) := by
  refine (integrable_exp_linear w z.re).mono' (by fun_prop) ?_
  exact ae_of_all _ fun y => by simp [Complex.norm_exp]

private lemma gaussian_transform (w : ℝ) (z : ℂ) :
    (∫ y : ℝ, Complex.exp (z * y) ∂gaussian w) =
      Complex.exp (z * (2 * w ^ 2) + (w ^ 2 : ℂ) * z ^ 2 / 4) := by
  have h := complexMGF_id_gaussianReal
    (μ := 2 * w ^ 2) (v := variance w) z
  change (∫ y : ℝ, Complex.exp (z * y) ∂gaussian w) = _ at h
  rw [h]
  congr 1
  simp only [variance, NNReal.coe_mk, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

private lemma gaussian_transform_norm (w a γ : ℝ) :
    ‖∫ y : ℝ, Complex.exp (frequency a γ * y) ∂gaussian w‖ =
      exp (w ^ 2 * (-2 * a + a ^ 2 / 4 - γ ^ 2 / 4)) := by
  rw [gaussian_transform, Complex.norm_exp]
  congr 1
  norm_num [frequency, pow_two, Complex.mul_re, Complex.mul_im, div_eq_mul_inv] <;> ring

private lemma gaussian_cancellation (w a γ : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (hγ : 10 ≤ |γ|) :
    ‖∫ y : ℝ, Complex.exp (frequency a γ * y) ∂gaussian w‖ ≤
      exp (-25 * w ^ 2) := by
  rw [gaussian_transform_norm]
  apply exp_le_exp.mpr
  have ha : a ^ 2 ≤ 2 * a := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha2)]
  have hg : 100 ≤ γ ^ 2 := by nlinarith [sq_abs γ, sq_nonneg (|γ| - 10)]
  have he : -2 * a + a ^ 2 / 4 - γ ^ 2 / 4 ≤ -25 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg w)]

private lemma restricted_exp_bound (w t u C : ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hC : 0 ≤ C) (hp : ∀ y ∈ S, exp (t * y) ≤ C * exp (u * y)) :
    (∫ y in S, exp (t * y) ∂gaussian w) ≤
      C * exp (2 * w ^ 2 * u + w ^ 2 * u ^ 2 / 4) := by
  have h := integral_mono
    ((integrable_exp_linear w t).indicator hS)
    ((integrable_exp_linear w u).const_mul C) (fun y => by
      by_cases hy : y ∈ S
      · simpa only [indicator_of_mem hy] using hp y hy
      · simp only [indicator_of_notMem hy]
        positivity)
  rw [integral_indicator hS, integral_const_mul, integral_exp_linear] at h
  exact h

private lemma lower_tail (H w a : ℝ) (hH : 0 ≤ H) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    (∫ y in Iio H, exp (-a * y) ∂gaussian w) ≤ exp (2 * H - 3 * w ^ 2) := by
  have h := restricted_exp_bound w (-a) (-2) (exp ((2 - a) * H))
    (Iio H) measurableSet_Iio (exp_nonneg _) (by
      intro y hy
      rw [← exp_add]
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hy.le)])
  rw [← exp_add] at h
  have he : (2 - a) * H + (2 * w ^ 2 * (-2) + w ^ 2 * (-2) ^ 2 / 4) =
      (2 - a) * H - 3 * w ^ 2 := by ring
  rw [he] at h
  exact h.trans (exp_le_exp.mpr (by nlinarith [mul_nonneg ha0 hH]))

private lemma upper_tail (w a : ℝ) (ha : 0 ≤ a) :
    (∫ y in Ioi (4 * w ^ 2), exp (-a * y) ∂gaussian w) ≤ exp (-4 * w ^ 2) := by
  have h := restricted_exp_bound w (-a) 4 (exp (-16 * w ^ 2))
    (Ioi (4 * w ^ 2)) measurableSet_Ioi (exp_nonneg _) (by
      intro y hy
      rw [← exp_add]
      apply exp_le_exp.mpr
      have hy0 : 0 ≤ y := (by positivity : 0 ≤ 4 * w ^ 2).trans hy.le
      have hy' : 4 * w ^ 2 ≤ y := hy.le
      nlinarith [mul_nonneg ha hy0])
  rw [← exp_add] at h
  convert h using 1 <;> congr 1 <;> ring

private lemma integral_three_intervals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure ℝ} {f : ℝ → E}
    (hf : Integrable f μ) {l u : ℝ} (hlu : l ≤ u) :
    (∫ y, f y ∂μ) = (∫ y in Icc l u, f y ∂μ) +
      (∫ y in Iio l, f y ∂μ) + (∫ y in Ioi u, f y ∂μ) := by
  have he : f = (fun y => (Icc l u).indicator f y +
      (Iio l).indicator f y + (Ioi u).indicator f y) := by
    funext y
    by_cases hl : y < l
    · have hu : ¬ u < y := by linarith
      simp [hl, hu, show ¬ (l ≤ y ∧ y ≤ u) by rintro ⟨h1, h2⟩; linarith]
    · by_cases hu : u < y
      · simp [hl, hu, show ¬ (l ≤ y ∧ y ≤ u) by rintro ⟨h1, h2⟩; linarith]
      · simp [hl, hu, show l ≤ y ∧ y ≤ u by constructor <;> linarith]
  conv_lhs => rw [he]
  have hcc := hf.indicator (s := Icc l u) measurableSet_Icc
  have hlo := hf.indicator (s := Iio l) measurableSet_Iio
  have hup := hf.indicator (s := Ioi u) measurableSet_Ioi
  simpa only [Pi.add_apply, integral_add hcc hlo,
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Iio,
    integral_indicator measurableSet_Ioi] using integral_add (hcc.add hlo) hup

theorem truncated_gaussian_cancellation (H a γ : ℝ) (hH : 20000 ≤ H)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hγ : 10 ≤ |γ|) :
    ‖∫ y in Icc H (4 * (H + 20) ^ 2),
        Complex.exp (frequency a γ * y) ∂gaussian (H + 20)‖ ≤
      exp (-25 * (H + 20) ^ 2) + exp (-H ^ 2) +
        exp (-4 * (H + 20) ^ 2) := by
  let w := H + 20
  let f : ℝ → ℂ := fun y => Complex.exp (frequency a γ * y)
  have hf := integrable_cexp_linear w (frequency a γ)
  have hHU : H ≤ 4 * w ^ 2 := by dsimp [w]; nlinarith [sq_nonneg H]
  have hs := integral_three_intervals hf hHU
  have he : (∫ y in Icc H (4 * w ^ 2), f y ∂gaussian w) =
      ((∫ y, f y ∂gaussian w) - (∫ y in Iio H, f y ∂gaussian w)) -
        (∫ y in Ioi (4 * w ^ 2), f y ∂gaussian w) := by
    dsimp [f] at hs ⊢
    linear_combination -hs
  have hlow : ‖∫ y in Iio H, f y ∂gaussian w‖ ≤ exp (-H ^ 2) := by
    calc
      _ ≤ ∫ y in Iio H, ‖f y‖ ∂gaussian w := norm_integral_le_integral_norm _
      _ = ∫ y in Iio H, exp (-a * y) ∂gaussian w := by
        simp [f, frequency, Complex.norm_exp]
      _ ≤ exp (2 * H - 3 * w ^ 2) := lower_tail H w a (by linarith) ha0 ha2
      _ ≤ exp (-H ^ 2) := by
        apply exp_le_exp.mpr
        dsimp [w]
        nlinarith [sq_nonneg H]
  have hupp : ‖∫ y in Ioi (4 * w ^ 2), f y ∂gaussian w‖ ≤ exp (-4 * w ^ 2) := by
    calc
      _ ≤ ∫ y in Ioi (4 * w ^ 2), ‖f y‖ ∂gaussian w := norm_integral_le_integral_norm _
      _ = ∫ y in Ioi (4 * w ^ 2), exp (-a * y) ∂gaussian w := by
        simp [f, frequency, Complex.norm_exp]
      _ ≤ _ := upper_tail w a ha0
  change ‖∫ y in Icc H (4 * w ^ 2), f y ∂gaussian w‖ ≤ _
  rw [he]
  have hn := (norm_sub_le
    ((∫ y, f y ∂gaussian w) - (∫ y in Iio H, f y ∂gaussian w))
    (∫ y in Ioi (4 * w ^ 2), f y ∂gaussian w)).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  exact hn.trans (by
    have hc := gaussian_cancellation w a γ ha0 ha2 hγ
    change ‖∫ y, f y ∂gaussian w‖ ≤ _ at hc
    linarith)

end D5.S3.Weil.Mertens.IntegratedExplicit.GaussianWindow
