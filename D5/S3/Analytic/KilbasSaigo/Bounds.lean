/- GID: D5/S3/Analytic/KilbasSaigo/Bounds
   generality: G
   mirror-B: D5/B/S3/Analytic/KilbasSaigo/Bounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Basic, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Mul, mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic]
   utility: none
   digest: Positivity and hyperbolic bounds from scaling equations and affine differential equations. -/

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set MeasureTheory
open scoped Topology

namespace D5.S3.Analytic.KilbasSaigo.Bounds

/-- A positive forcing and a nonnegative contraction kernel exclude a nonpositive minimum. -/
private lemma positive_of_scaling {f c p K L : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0))
    (hc : ∀ x ≥ 0, 0 < c x) (hp : ∀ x ≥ 0, 0 < p x)
    (hK : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ K r)
    (hL : ∀ r ∈ Ioo (0 : ℝ) 1, L r ∈ Icc (0 : ℝ) 1)
    (heq : ∀ x ≥ 0, c x * f x = p x +
      ∫ r in Ioo (0 : ℝ) 1, (f (L r * x) - f x) * K r) :
    ∀ x ≥ 0, 0 < f x := by
  intro x hx
  by_contra hn
  have hn : f x ≤ 0 := le_of_not_gt hn
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hx)
    (hf.mono (fun z hz => hz.1))
  have hyf : f y ≤ 0 := (hmin ⟨hx, le_rfl⟩).trans hn
  have hi : 0 ≤ ∫ r in Ioo (0 : ℝ) 1, (f (L r * y) - f y) * K r := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply mul_nonneg _ (hK r hr)
    apply sub_nonneg.mpr
    apply hmin
    exact ⟨mul_nonneg (hL r hr).1 hy.1,
      (mul_le_of_le_one_left hy.1 (hL r hr).2).trans hy.2⟩
  have := heq y hy.1
  have := mul_nonpos_of_nonneg_of_nonpos (hc y hy.1).le hyf
  linarith [hp y hy.1]

/-- A positive source in a degenerate first-order equation preserves strict positivity. -/
private lemma positive_of_ode {f f' c p : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hf0 : 0 < f 0)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hc : ∀ x ≥ 0, 0 < c x) (hp : ∀ x ≥ 0, 0 < p x)
    (heq : ∀ x ≥ 0, b * x * f' x + c x * f x = p x) :
    ∀ x ≥ 0, 0 < f x := by
  intro x hx
  by_contra hn
  have hn : f x ≤ 0 := le_of_not_gt hn
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun z => (hf z).continuousAt)
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hx)
    hcont.continuousOn
  have hyf : f y ≤ 0 := (hmin ⟨hx, le_rfl⟩).trans hn
  have hy0 : 0 < y := lt_of_le_of_ne hy.1 (by rintro rfl; linarith)
  have ht : (0 : ℝ) - y ∈ posTangentConeAt (Icc 0 x) y := by
    apply sub_mem_posTangentConeAt_of_segment_subset
    exact (convex_Icc 0 x).segment_subset hy ⟨le_rfl, hx⟩
  have hd := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    (hf y).hasFDerivAt.hasFDerivWithinAt ht
  have hd' : f' y ≤ 0 := by
    change 0 ≤ (0 - y) * f' y at hd
    nlinarith
  have ht1 := mul_nonpos_of_nonneg_of_nonpos (mul_pos hb hy0).le hd'
  have ht2 := mul_nonpos_of_nonneg_of_nonpos (hc y hy.1).le hyf
  linarith [heq y hy.1, hp y hy.1]

/-- Monotonicity and convexity turn a scaling equation into hyperbolic bounds. -/
private lemma hyperbolic_of_scaling {f K L : ℝ → ℝ} {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hf0 : f 0 = 1)
    (hanti : AntitoneOn f (Ici 0)) (hconv : ConvexOn ℝ (Ici 0) f)
    (hK : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ K r)
    (hL : ∀ r ∈ Ioo (0 : ℝ) 1, L r ∈ Icc (0 : ℝ) 1)
    (hint : IntegrableOn (fun r => (1 - L r) * K r) (Ioo (0 : ℝ) 1))
    (hmoment : ∫ r in Ioo (0 : ℝ) 1, (1 - L r) * K r = q - p)
    (heq : ∀ x ≥ 0, (p + x) * f x = p +
      ∫ r in Ioo (0 : ℝ) 1, (f (L r * x) - f x) * K r) :
    ∀ x ≥ 0, p / (p + x) ≤ f x ∧ f x ≤ q / (q + x) := by
  intro x hx
  have hpoint (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      0 ≤ (f (L r * x) - f x) * K r ∧
      (f (L r * x) - f x) * K r ≤ (1 - f x) * ((1 - L r) * K r) := by
    have hscale := hL r hr
    have hd := hanti (mul_nonneg hscale.1 hx) hx
      (mul_le_of_le_one_left hx hscale.2)
    have hc := hconv.2 (show (0 : ℝ) ∈ Ici 0 by simp) hx
      (sub_nonneg.mpr hscale.2) hscale.1 (by ring : 1 - L r + L r = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, hf0, mul_one] at hc
    refine ⟨mul_nonneg (sub_nonneg.mpr hd) (hK r hr), ?_⟩
    have := mul_le_mul_of_nonneg_right (show f (L r * x) - f x ≤
      (1 - f x) * (1 - L r) by nlinarith) (hK r hr)
    nlinarith
  have hi0 : 0 ≤ ∫ r in Ioo (0 : ℝ) 1, (f (L r * x) - f x) * K r := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hpoint r hr).1
  have hi1 : (∫ r in Ioo (0 : ℝ) 1, (f (L r * x) - f x) * K r) ≤
      (1 - f x) * (q - p) := by
    rw [← hmoment, ← integral_const_mul]
    apply integral_mono_of_nonneg _ (hint.const_mul (1 - f x))
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hpoint r hr).2
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hpoint r hr).1
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < p + x)).mpr
    nlinarith [heq x hx]
  · apply (le_div_iff₀ (by linarith : 0 < q + x)).mpr
    nlinarith [heq x hx]

/-- A decreasing convex solution of the affine ODE satisfies both hyperbolic bounds. -/
private lemma hyperbolic_of_ode {f f' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hf0 : f 0 = 1)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hneg : ∀ x ≥ 0, f' x ≤ 0) (hconv : ConvexOn ℝ (Ici 0) f)
    (heq : ∀ x ≥ 0, b * x * f' x + (a + x) * f x = a) :
    ∀ x ≥ 0, a / (a + x) ≤ f x ∧ f x ≤ (a + b) / (a + b + x) := by
  intro x hx
  have htan : f x - x * f' x ≤ 1 := by
    rcases hx.eq_or_lt with rfl | hxpos
    · simp [hf0]
    · have ht := hconv.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Ici 0 by simp) hx hxpos (hf x)
      rw [slope_def_field, hf0, sub_zero] at ht
      have ht := (div_le_iff₀ hxpos).mp ht
      nlinarith
  have hs := heq x hx
  have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb.le hx) (hneg x hx)
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < a + x)).mpr
    nlinarith
  · apply (le_div_iff₀ (by linarith : 0 < a + b + x)).mpr
    nlinarith [mul_le_mul_of_nonneg_left htan hb.le]

end D5.S3.Analytic.KilbasSaigo.Bounds
