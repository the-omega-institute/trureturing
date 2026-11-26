/- GID: D5/S3/Analytic/Dilation/DuplicationQuadraticGerm
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/DuplicationQuadraticGerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bounded duplication solution is determined by its quadratic germ at zero. -/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Bounded duplication solutions are determined globally by their quadratic germ. -/

namespace D5.S3.Analytic.Dilation.DuplicationQuadraticGerm

open Filter Asymptotics
open scoped Topology

private theorem duplication_error (f g : ℝ → ℝ)
    (hf : ∀ t, |f t| ≤ 1) (hg : ∀ t, |g t| ≤ 1)
    (hfd : ∀ t, f (2 * t) = 2 * (f t) ^ 2 - 1)
    (hgd : ∀ t, g (2 * t) = 2 * (g t) ^ 2 - 1) (t : ℝ) :
    |f (2 * t) - g (2 * t)| ≤ 4 * |f t - g t| := by
  have hsum : |f t + g t| ≤ 2 := by
    calc
      |f t + g t| ≤ |f t| + |g t| := abs_add_le _ _
      _ ≤ 2 := by linarith [hf t, hg t]
  rw [hfd, hgd]
  calc
    |2 * f t ^ 2 - 1 - (2 * g t ^ 2 - 1)| =
        |2 * (f t - g t) * (f t + g t)| := congrArg abs (by ring)
    _ = 2 * |f t - g t| * |f t + g t| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * |f t - g t| * 2 :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) (abs_nonneg _))
    _ = 4 * |f t - g t| := by ring

private theorem dyadic_error (f g : ℝ → ℝ)
    (hf : ∀ t, |f t| ≤ 1) (hg : ∀ t, |g t| ≤ 1)
    (hfd : ∀ t, f (2 * t) = 2 * (f t) ^ 2 - 1)
    (hgd : ∀ t, g (2 * t) = 2 * (g t) ^ 2 - 1) (n : ℕ) (t : ℝ) :
    |f ((2 : ℝ) ^ n * t) - g ((2 : ℝ) ^ n * t)| ≤
      ((2 : ℝ) ^ n) ^ 2 * |f t - g t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have harg : (2 : ℝ) ^ (n + 1) * t = 2 * (2 ^ n * t) := by
      rw [pow_succ]
      ring
    rw [harg]
    calc
      |f (2 * (2 ^ n * t)) - g (2 * (2 ^ n * t))| ≤
          4 * |f (2 ^ n * t) - g (2 ^ n * t)| :=
        duplication_error f g hf hg hfd hgd _
      _ ≤ 4 * (((2 : ℝ) ^ n) ^ 2 * |f t - g t|) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = ((2 : ℝ) ^ (n + 1)) ^ 2 * |f t - g t| := by
        rw [pow_succ]
        ring

private theorem eq_of_duplication_of_sub_isLittleO_sq (f g : ℝ → ℝ)
    (hf : ∀ t, |f t| ≤ 1) (hg : ∀ t, |g t| ≤ 1)
    (hfd : ∀ t, f (2 * t) = 2 * (f t) ^ 2 - 1)
    (hgd : ∀ t, g (2 * t) = 2 * (g t) ^ 2 - 1)
    (hsmall : (fun t => f t - g t) =o[𝓝 0] (fun t => t ^ 2)) (t : ℝ) :
    f t = g t := by
  apply eq_of_forall_dist_le
  intro ε hε
  have hden : 0 < t ^ 2 + 1 := by positivity
  have hscale : Tendsto (fun n : ℕ => t / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ 2⁻¹ by norm_num) (by norm_num)).const_mul t
  obtain ⟨n, hn⟩ := (hscale.eventually (hsmall.def (div_pos hε hden))).exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (t / (2 : ℝ) ^ n))] at hn
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg : (2 : ℝ) ^ n * (t / (2 : ℝ) ^ n) = t := by field_simp
  have hb := dyadic_error f g hf hg hfd hgd n (t / (2 : ℝ) ^ n)
  rw [harg] at hb
  calc
    dist (f t) (g t) = |f t - g t| := Real.dist_eq _ _
    _ ≤ ((2 : ℝ) ^ n) ^ 2 * |f (t / (2 : ℝ) ^ n) - g (t / (2 : ℝ) ^ n)| := hb
    _ ≤ ((2 : ℝ) ^ n) ^ 2 * (ε / (t ^ 2 + 1) * (t / (2 : ℝ) ^ n) ^ 2) :=
      mul_le_mul_of_nonneg_left hn (sq_nonneg _)
    _ = ε * t ^ 2 / (t ^ 2 + 1) := by field_simp
    _ ≤ ε := by
      rw [div_le_iff₀ hden]
      nlinarith

/-- The cosine remainder at zero is little-o of the square, including the value at zero. -/
theorem cosine_quadratic_germ (k : ℝ) :
    (fun t : ℝ => Real.cos (k * t) - (1 - (k ^ 2 / 2) * t ^ 2))
      =o[𝓝 0] (fun t => t ^ 2) := by
  have hsin (x : ℝ) : Real.sinc x * x = Real.sin x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx, div_mul_cancel₀ _ hx]
  have hc (t : ℝ) : Real.cos (k * t) =
      1 - 2 * (Real.sinc (k * t / 2) * (k * t / 2)) ^ 2 := by
    rw [hsin]
    have harg : 2 * (k * t / 2) = k * t := by ring
    simpa only [harg] using Real.cos_two_mul_eq_one_sub (k * t / 2)
  have ht : Tendsto
      (fun t : ℝ => (k ^ 2 / 2) * (1 - Real.sinc (k * t / 2) ^ 2))
      (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt
        (fun t : ℝ => (k ^ 2 / 2) * (1 - Real.sinc (k * t / 2) ^ 2)) 0 := by
      fun_prop
    simpa using hcont.tendsto
  have ho := ((isLittleO_one_iff ℝ).mpr ht).mul_isBigO
    (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0))
  apply ho.congr
  · intro t
    rw [hc]
    ring
  · intro t
    simp

/-- A bounded solution of the duplication equation with the cosine quadratic germ is cosine.
The germ is taken in the full neighborhood filter at zero, so it includes the value at zero. -/
theorem eq_cos_of_quadratic_germ {f : ℝ → ℝ} {k : ℝ}
    (hbound : ∀ t, |f t| ≤ 1)
    (hdup : ∀ t, f (2 * t) = 2 * (f t) ^ 2 - 1)
    (hgerm : (fun t => f t - (1 - (k ^ 2 / 2) * t ^ 2))
      =o[𝓝 0] (fun t => t ^ 2)) (t : ℝ) :
    f t = Real.cos (k * t) := by
  apply eq_of_duplication_of_sub_isLittleO_sq f (fun s => Real.cos (k * s))
    hbound (fun s => Real.abs_cos_le_one _) hdup
  · intro s
    rw [show k * (2 * s) = 2 * (k * s) by ring, Real.cos_two_mul]
  · exact (hgerm.sub (cosine_quadratic_germ k)).congr_left (fun s => by ring)

end D5.S3.Analytic.Dilation.DuplicationQuadraticGerm
