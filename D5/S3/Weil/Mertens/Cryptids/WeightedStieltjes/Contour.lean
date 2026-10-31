/- GID: D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Contour
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Contour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids WeightedStieltjes analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/WeightedStieltjes.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Residues

/-! Original WeightedStieltjes analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.WeightedStieltjes

open Complex Finset Filter MeasureTheory Set Asymptotics Topology
open scoped Real Topology Interval

/-- Horizontal line integral of `1 / (σ + y * I - p)` when `y ≠ p.im`. -/
theorem horizontal_integral_inv_sub_eq {y : ℝ} {p : ℂ} (hy : y ≠ p.im) (c₁ c₂ : ℝ) :
    (∫ σ : ℝ in c₁..c₂, 1 / ((σ : ℂ) + (y : ℂ) * I - p)) =
      horizPoleAntideriv (y - p.im) p.re c₂ - horizPoleAntideriv (y - p.im) p.re c₁ := by
  have h_fn :
      (fun σ : ℝ ↦ 1 / ((σ : ℂ) + (y : ℂ) * I - p)) =
        fun σ : ℝ ↦ 1 / (((σ - p.re : ℝ) : ℂ) + ((y - p.im : ℝ) : ℂ) * I) := by
    ext σ
    rw [horizontal_sub_eq]
  rw [h_fn]
  exact intervalIntegral_one_div_add_mul_I (sub_ne_zero.mpr hy) c₁ c₂

/-!
## Section 2: The 4-Corner `log` + `arctan` Cancellation (`rectBoundaryIntegral = 2πi`)
-/

/-- Complementary arctangent identity: for `0 < x` and `0 < y`,
$$\arctan\left(\frac{y}{x}\right) + \arctan\left(\frac{x}{y}\right) = \frac{\pi}{2}.$$ -/
theorem arctan_div_add_arctan_div_eq_pi_div_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.arctan (y / x) + Real.arctan (x / y) = Real.pi / 2 := by
  have h_inv : x / y = (y / x)⁻¹ := (inv_div y x).symm
  rw [h_inv, Real.arctan_inv_of_pos (div_pos hy hx)]
  ring

/-- **The 4-Corner `log` + `arctan` Rectangle Integral Identity**:
For any point `p ∈ ℂ` strictly inside the rectangle `[c₁, c₂] × [-T, T]`
(`c₁ < p.re < c₂` and `-T < p.im < T`),
$$\operatorname{rectBoundaryIntegral}\left(s \mapsto \frac{1}{s - p}\right) c_1\, c_2\, T = 2\pi
i.$$ -/
theorem rectBoundaryIntegral_inv_sub_eq_two_pi_I {c₁ c₂ T : ℝ} {p : ℂ}
    (hre₁ : c₁ < p.re) (hre₂ : p.re < c₂) (him₁ : -T < p.im) (him₂ : p.im < T) :
    rectBoundaryIntegral (fun s ↦ 1 / (s - p)) c₁ c₂ T = 2 * π * I := by
  unfold rectBoundaryIntegral
  have h_bot_fn :
      (fun σ : ℝ ↦ 1 / ((σ : ℂ) - (T : ℂ) * I - p)) =
        fun σ : ℝ ↦ 1 / ((σ : ℂ) + ((-T : ℝ) : ℂ) * I - p) := by
    ext σ
    push_cast
    ring_nf
  rw [h_bot_fn,
    mul_I_vertical_integral_inv_sub_eq hre₂.ne' T,
    mul_I_vertical_integral_inv_sub_eq hre₁.ne T,
    horizontal_integral_inv_sub_eq him₂.ne' c₁ c₂,
    horizontal_integral_inv_sub_eq him₁.ne c₁ c₂]
  simp only [vertPoleAntideriv, horizPoleAntideriv]
  set A : ℝ := c₂ - p.re
  set B : ℝ := p.re - c₁
  set C : ℝ := T - p.im
  set D : ℝ := T + p.im
  have hA : 0 < A := sub_pos.mpr hre₂
  have hB : 0 < B := sub_pos.mpr hre₁
  have hC : 0 < C := sub_pos.mpr him₂
  have hD : 0 < D := by dsimp [D]; linarith
  have hc₁_sub : c₁ - p.re = -B := by dsimp [B]; ring
  have hnegT_sub : -T - p.im = -D := by dsimp [D]; ring
  rw [hc₁_sub, hnegT_sub]
  have h_sq_B : (-B) ^ 2 = B ^ 2 := neg_sq B
  have h_sq_D : (-D) ^ 2 = D ^ 2 := neg_sq D
  have h_div1 : (-D) / A = -(D / A) := neg_div A D
  have h_div2 : C / (-B) = -(C / B) := div_neg C
  have h_div3 : (-D) / (-B) = D / B := neg_div_neg_eq D B
  have h_div4 : (-B) / C = -(B / C) := neg_div C B
  have h_div5 : A / (-D) = -(A / D) := div_neg A
  have h_div6 : (-B) / (-D) = B / D := neg_div_neg_eq B D
  rw [h_sq_B, h_sq_D, h_div1, h_div2, h_div3, h_div4, h_div5, h_div6]
  simp only [Real.arctan_neg, Complex.ofReal_neg]
  have h_pair1 := arctan_div_add_arctan_div_eq_pi_div_two hA hC
  have h_pair2 := arctan_div_add_arctan_div_eq_pi_div_two hA hD
  have h_pair3 := arctan_div_add_arctan_div_eq_pi_div_two hB hC
  have h_pair4 := arctan_div_add_arctan_div_eq_pi_div_two hB hD
  have h_sum_arctan :
      ((Real.arctan (C / A) : ℂ) + (Real.arctan (A / C) : ℂ)) +
        ((Real.arctan (D / A) : ℂ) + (Real.arctan (A / D) : ℂ)) +
        ((Real.arctan (C / B) : ℂ) + (Real.arctan (B / C) : ℂ)) +
        ((Real.arctan (D / B) : ℂ) + (Real.arctan (B / D) : ℂ)) = 2 * π := by
    norm_cast
    linarith
  linear_combination I * h_sum_arctan

/-- Corollary for a general residue `r : ℂ` at an interior pole `p`:
$$\operatorname{rectBoundaryIntegral}\left(s \mapsto \frac{r}{s - p}\right) c_1\, c_2\, T = 2\pi i
r.$$ -/
theorem rectBoundaryIntegral_div_sub_eq_two_pi_I_mul {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ)
    (hre₁ : c₁ < p.re) (hre₂ : p.re < c₂) (him₁ : -T < p.im) (him₂ : p.im < T) :
    rectBoundaryIntegral (fun s ↦ r / (s - p)) c₁ c₂ T = 2 * π * I * r := by
  have h_eq : (fun s : ℂ ↦ r / (s - p)) = fun s : ℂ ↦ r * (1 / (s - p)) := by
    ext s; ring
  rw [h_eq, rectBoundaryIntegral_const_mul,
    rectBoundaryIntegral_inv_sub_eq_two_pi_I hre₁ hre₂ him₁ him₂]
  ring

/-!
## Section 3: Rectangle Vanishing for Holomorphic Functions (`rectBoundaryIntegral = 0`)
-/

/-- The closed rectangle `[c₁, c₂] ×ℂ [-T, T]` in `ℂ`. -/
def closedRect (c₁ c₂ T : ℝ) : Set ℂ :=
  Set.Icc c₁ c₂ ×ℂ Set.Icc (-T) T

/-- The open rectangle `(c₁, c₂) ×ℂ (-T, T)` in `ℂ`. -/
def openRect (c₁ c₂ T : ℝ) : Set ℂ :=
  Set.Ioo c₁ c₂ ×ℂ Set.Ioo (-T) T

@[simp]
theorem mem_closedRect {c₁ c₂ T : ℝ} {s : ℂ} :
    s ∈ closedRect c₁ c₂ T ↔ (c₁ ≤ s.re ∧ s.re ≤ c₂) ∧ (-T ≤ s.im ∧ s.im ≤ T) :=
  Iff.rfl

@[simp]
theorem mem_openRect {c₁ c₂ T : ℝ} {s : ℂ} :
    s ∈ openRect c₁ c₂ T ↔ (c₁ < s.re ∧ s.re < c₂) ∧ (-T < s.im ∧ s.im < T) :=
  Iff.rfl

/-- Connection between `rectBoundaryIntegral F c₁ c₂ T` and the expression in
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` with corners
`z = c₁ - T * I` and `w = c₂ + T * I`. -/
theorem rectBoundaryIntegral_eq_cauchy_boundary (F : ℂ → ℂ) (c₁ c₂ T : ℝ) :
    rectBoundaryIntegral F c₁ c₂ T =
      (∫ x : ℝ in ((c₁ : ℂ) - (T : ℂ) * I).re..((c₂ : ℂ) + (T : ℂ) * I).re,
          F (x + ((c₁ : ℂ) - (T : ℂ) * I).im * I)) -
        (∫ x : ℝ in ((c₁ : ℂ) - (T : ℂ) * I).re..((c₂ : ℂ) + (T : ℂ) * I).re,
          F (x + ((c₂ : ℂ) + (T : ℂ) * I).im * I)) +
        I • (∫ y : ℝ in ((c₁ : ℂ) - (T : ℂ) * I).im..((c₂ : ℂ) + (T : ℂ) * I).im,
          F (((c₂ : ℂ) + (T : ℂ) * I).re + y * I)) -
        I • (∫ y : ℝ in ((c₁ : ℂ) - (T : ℂ) * I).im..((c₂ : ℂ) + (T : ℂ) * I).im,
          F (((c₁ : ℂ) - (T : ℂ) * I).re + y * I)) := by
  unfold rectBoundaryIntegral
  simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    sub_zero, add_re, add_zero, sub_im, mul_im, zero_add, zero_sub, ofReal_neg, neg_mul,
    add_im, smul_eq_mul]
  have h_bot :
      (fun x : ℝ ↦ F ((x : ℂ) + -((T : ℂ) * I))) =
        fun x : ℝ ↦ F ((x : ℂ) - (T : ℂ) * I) := by
    ext x; ring_nf
  rw [h_bot]
  ring

/-- **Rectangle Vanishing off a Countable Set**:
If `F : ℂ → ℂ` is continuous on `closedRect c₁ c₂ T` (`c₁ ≤ c₂`, `0 ≤ T`) and complex-differentiable
on `openRect c₁ c₂ T \ s` for a countable set `s : Set ℂ`, then
$$\operatorname{rectBoundaryIntegral} F\, c_1\, c_2\, T = 0.$$ -/
theorem rectBoundaryIntegral_eq_zero_of_differentiable_on_off_countable {c₁ c₂ T : ℝ}
    (hc : c₁ ≤ c₂) (hT : 0 ≤ T) {F : ℂ → ℂ} {s : Set ℂ} (hs : s.Countable)
    (hcont : ContinuousOn F (closedRect c₁ c₂ T))
    (hdiff : ∀ z ∈ openRect c₁ c₂ T \ s, DifferentiableAt ℂ F z) :
    rectBoundaryIntegral F c₁ c₂ T = 0 := by
  rw [rectBoundaryIntegral_eq_cauchy_boundary]
  set z : ℂ := (c₁ : ℂ) - (T : ℂ) * I
  set w : ℂ := (c₂ : ℂ) + (T : ℂ) * I
  have hz_re : z.re = c₁ := by simp [z]
  have hw_re : w.re = c₂ := by simp [w]
  have hz_im : z.im = -T := by simp [z]
  have hw_im : w.im = T := by simp [w]
  have h_negT_le : -T ≤ T := by linarith
  have h_closed : [[z.re, w.re]] ×ℂ [[z.im, w.im]] = closedRect c₁ c₂ T := by
    rw [hz_re, hw_re, hz_im, hw_im, uIcc_of_le hc, uIcc_of_le h_negT_le, closedRect]
  have h_open :
      Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) =
        openRect c₁ c₂ T := by
    rw [hz_re, hw_re, hz_im, hw_im, min_eq_left hc, max_eq_right hc,
      min_eq_left h_negT_le, max_eq_right h_negT_le, openRect]
  exact Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable F z w s hs
    (by rwa [h_closed]) (by rwa [h_open])

/-- No point on the right or left vertical boundary lines `c + t * I` (`c = c₁` or `c = c₂`)
lies in `openRect c₁ c₂ T`. -/
theorem vertical_not_mem_openRect_left (c₁ c₂ T t : ℝ) :
    ((c₁ : ℂ) + (t : ℂ) * I) ∉ openRect c₁ c₂ T := by
  rw [mem_openRect]
  simp

theorem vertical_not_mem_openRect_right (c₁ c₂ T t : ℝ) :
    ((c₂ : ℂ) + (t : ℂ) * I) ∉ openRect c₁ c₂ T := by
  rw [mem_openRect]
  simp

/-- No point on the top or bottom horizontal boundary lines `σ ± T * I` lies in
`openRect c₁ c₂ T`. -/
theorem horizontal_not_mem_openRect_top (c₁ c₂ T σ : ℝ) :
    ((σ : ℂ) + (T : ℂ) * I) ∉ openRect c₁ c₂ T := by
  rw [mem_openRect]
  simp

theorem horizontal_not_mem_openRect_bot (c₁ c₂ T σ : ℝ) :
    ((σ : ℂ) - (T : ℂ) * I) ∉ openRect c₁ c₂ T := by
  rw [mem_openRect]
  simp

/-- Every point on the four boundary segments of `[c₁, c₂] × [-T, T]` (`c₁ ≤ c₂`, `0 ≤ T`)
belongs to `closedRect c₁ c₂ T`. -/
theorem vertical_mem_closedRect_left {c₁ c₂ T t : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    (ht : t ∈ Set.uIcc (-T) T) :
    ((c₁ : ℂ) + (t : ℂ) * I) ∈ closedRect c₁ c₂ T := by
  rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
  rw [mem_closedRect]
  simp [hc, ht.1, ht.2]

theorem vertical_mem_closedRect_right {c₁ c₂ T t : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    (ht : t ∈ Set.uIcc (-T) T) :
    ((c₂ : ℂ) + (t : ℂ) * I) ∈ closedRect c₁ c₂ T := by
  rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
  rw [mem_closedRect]
  simp [hc, ht.1, ht.2]

theorem horizontal_mem_closedRect_top {c₁ c₂ T σ : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    (hσ : σ ∈ Set.uIcc c₁ c₂) :
    ((σ : ℂ) + (T : ℂ) * I) ∈ closedRect c₁ c₂ T := by
  rw [Set.uIcc_of_le hc] at hσ
  have h_negT : -T ≤ T := by linarith
  rw [mem_closedRect]
  simp [hσ.1, hσ.2, h_negT]

theorem horizontal_mem_closedRect_bot {c₁ c₂ T σ : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    (hσ : σ ∈ Set.uIcc c₁ c₂) :
    ((σ : ℂ) - (T : ℂ) * I) ∈ closedRect c₁ c₂ T := by
  rw [Set.uIcc_of_le hc] at hσ
  have h_negT : -T ≤ T := by linarith
  rw [mem_closedRect]
  simp [hσ.1, hσ.2, h_negT]

/-- If `M₁` and `M₂` agree on `closedRect c₁ c₂ T \ P` where `P ⊆ openRect c₁ c₂ T` (`c₁ ≤ c₂`,
`0 ≤ T`), then `rectBoundaryIntegral M₁ c₁ c₂ T = rectBoundaryIntegral M₂ c₁ c₂ T`. -/
theorem rectBoundaryIntegral_congr_of_eqOn_sdiff {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {M₁ M₂ : ℂ → ℂ} {P : Set ℂ} (hP : P ⊆ openRect c₁ c₂ T)
    (heq : Set.EqOn M₁ M₂ (closedRect c₁ c₂ T \ P)) :
    rectBoundaryIntegral M₁ c₁ c₂ T = rectBoundaryIntegral M₂ c₁ c₂ T := by
  unfold rectBoundaryIntegral
  have h1 :
      (∫ t in (-T)..T, M₁ ((c₂ : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T, M₂ ((c₂ : ℂ) + (t : ℂ) * I) :=
    intervalIntegral.integral_congr fun t ht ↦
      heq ⟨vertical_mem_closedRect_right hc hT ht,
        fun hp ↦ vertical_not_mem_openRect_right c₁ c₂ T t (hP hp)⟩
  have h2 :
      (∫ t in (-T)..T, M₁ ((c₁ : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T, M₂ ((c₁ : ℂ) + (t : ℂ) * I) :=
    intervalIntegral.integral_congr fun t ht ↦
      heq ⟨vertical_mem_closedRect_left hc hT ht,
        fun hp ↦ vertical_not_mem_openRect_left c₁ c₂ T t (hP hp)⟩
  have h3 :
      (∫ σ in c₁..c₂, M₁ ((σ : ℂ) + (T : ℂ) * I)) =
        ∫ σ in c₁..c₂, M₂ ((σ : ℂ) + (T : ℂ) * I) :=
    intervalIntegral.integral_congr fun σ hσ ↦
      heq ⟨horizontal_mem_closedRect_top hc hT hσ,
        fun hp ↦ horizontal_not_mem_openRect_top c₁ c₂ T σ (hP hp)⟩
  have h4 :
      (∫ σ in c₁..c₂, M₁ ((σ : ℂ) - (T : ℂ) * I)) =
        ∫ σ in c₁..c₂, M₂ ((σ : ℂ) - (T : ℂ) * I) :=
    intervalIntegral.integral_congr fun σ hσ ↦
      heq ⟨horizontal_mem_closedRect_bot hc hT hσ,
        fun hp ↦ horizontal_not_mem_openRect_bot c₁ c₂ T σ (hP hp)⟩
  rw [h1, h2, h3, h4]

/-- For any pole `p ∈ openRect c₁ c₂ T` and residue `r : ℂ`, `s ↦ r / (s - p)` is continuous on
each of the four boundary lines of `[c₁, c₂] × [-T, T]`, hence `IntervalIntegrable`. -/
theorem intervalIntegrable_pole_right {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ) (hp : p ∈ openRect c₁ c₂ T) :
    IntervalIntegrable (fun t : ℝ ↦ r / ((c₂ : ℂ) + (t : ℂ) * I - p)) volume (-T) T := by
  refine (continuous_const.div ?_ fun t ↦ ?_).intervalIntegrable (-T) T
  · fun_prop
  · rw [vertical_sub_eq]
    exact complex_add_mul_I_ne_zero_of_left (sub_ne_zero.mpr hp.1.2.ne')

theorem intervalIntegrable_pole_left {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ) (hp : p ∈ openRect c₁ c₂ T) :
    IntervalIntegrable (fun t : ℝ ↦ r / ((c₁ : ℂ) + (t : ℂ) * I - p)) volume (-T) T := by
  refine (continuous_const.div ?_ fun t ↦ ?_).intervalIntegrable (-T) T
  · fun_prop
  · rw [vertical_sub_eq]
    exact complex_add_mul_I_ne_zero_of_left (sub_ne_zero.mpr hp.1.1.ne)

theorem intervalIntegrable_pole_top {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ) (hp : p ∈ openRect c₁ c₂ T) :
    IntervalIntegrable (fun σ : ℝ ↦ r / ((σ : ℂ) + (T : ℂ) * I - p)) volume c₁ c₂ := by
  refine (continuous_const.div ?_ fun σ ↦ ?_).intervalIntegrable c₁ c₂
  · fun_prop
  · rw [horizontal_sub_eq]
    exact complex_add_mul_I_ne_zero_of_right (sub_ne_zero.mpr hp.2.2.ne')

theorem intervalIntegrable_pole_bot {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ) (hp : p ∈ openRect c₁ c₂ T) :
    IntervalIntegrable (fun σ : ℝ ↦ r / ((σ : ℂ) - (T : ℂ) * I - p)) volume c₁ c₂ := by
  refine (continuous_const.div ?_ fun σ ↦ ?_).intervalIntegrable c₁ c₂
  · fun_prop
  · have h_eq : (σ : ℂ) - (T : ℂ) * I - p = (σ : ℂ) + ((-T : ℝ) : ℂ) * I - p := by
      push_cast; ring
    rw [h_eq, horizontal_sub_eq]
    exact complex_add_mul_I_ne_zero_of_right (sub_ne_zero.mpr hp.2.1.ne)

/-- If `F : ℂ → ℂ` is continuous on `closedRect c₁ c₂ T` (`c₁ ≤ c₂`, `0 ≤ T`), then `F` is
`IntervalIntegrable` along all four boundary segments of `[c₁, c₂] × [-T, T]`. -/
theorem intervalIntegrable_right_of_continuousOn {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T)) :
    IntervalIntegrable (fun t : ℝ ↦ F ((c₂ : ℂ) + (t : ℂ) * I)) volume (-T) T := by
  refine (hcont.comp (by fun_prop) ?_).intervalIntegrable
  intro t ht
  exact vertical_mem_closedRect_right hc hT ht

theorem intervalIntegrable_left_of_continuousOn {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T)) :
    IntervalIntegrable (fun t : ℝ ↦ F ((c₁ : ℂ) + (t : ℂ) * I)) volume (-T) T := by
  refine (hcont.comp (by fun_prop) ?_).intervalIntegrable
  intro t ht
  exact vertical_mem_closedRect_left hc hT ht

theorem intervalIntegrable_top_of_continuousOn {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T)) :
    IntervalIntegrable (fun σ : ℝ ↦ F ((σ : ℂ) + (T : ℂ) * I)) volume c₁ c₂ := by
  refine (hcont.comp (by fun_prop) ?_).intervalIntegrable
  intro σ hσ
  exact horizontal_mem_closedRect_top hc hT hσ

theorem intervalIntegrable_bot_of_continuousOn {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T)) :
    IntervalIntegrable (fun σ : ℝ ↦ F ((σ : ℂ) - (T : ℂ) * I)) volume c₁ c₂ := by
  refine (hcont.comp (by fun_prop) ?_).intervalIntegrable
  intro σ hσ
  exact horizontal_mem_closedRect_bot hc hT hσ

/-- Additivity of `rectBoundaryIntegral` for `F` continuous on `closedRect c₁ c₂ T` plus a finite
sum of interior poles `∑ p ∈ P, r p / (s - p)`. -/
theorem rectBoundaryIntegral_add_sum_poles {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T))
    (P : Finset ℂ) (r : ℂ → ℂ) (hP : ∀ p ∈ P, p ∈ openRect c₁ c₂ T) :
    rectBoundaryIntegral (fun s ↦ F s + ∑ p ∈ P, r p / (s - p)) c₁ c₂ T =
      rectBoundaryIntegral F c₁ c₂ T +
        ∑ p ∈ P, rectBoundaryIntegral (fun s ↦ r p / (s - p)) c₁ c₂ T := by
  unfold rectBoundaryIntegral
  have h_sum_right :
      IntervalIntegrable (fun t : ℝ ↦ ∑ p ∈ P,
        r p / ((c₂ : ℂ) + (t : ℂ) * I - p)) volume (-T) T := by
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum P fun p hp ↦ intervalIntegrable_pole_right (r p) (hP p hp)
  have h_sum_left :
      IntervalIntegrable (fun t : ℝ ↦ ∑ p ∈ P,
        r p / ((c₁ : ℂ) + (t : ℂ) * I - p)) volume (-T) T := by
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum P fun p hp ↦ intervalIntegrable_pole_left (r p) (hP p hp)
  have h_sum_top :
      IntervalIntegrable (fun σ : ℝ ↦ ∑ p ∈ P, r p / ((σ : ℂ) + (T : ℂ) * I - p)) volume c₁ c₂ := by
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum P fun p hp ↦ intervalIntegrable_pole_top (r p) (hP p hp)
  have h_sum_bot :
      IntervalIntegrable (fun σ : ℝ ↦ ∑ p ∈ P, r p / ((σ : ℂ) - (T : ℂ) * I - p)) volume c₁ c₂ := by
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum P fun p hp ↦ intervalIntegrable_pole_bot (r p) (hP p hp)
  rw [intervalIntegral.integral_add (intervalIntegrable_right_of_continuousOn hc hT hcont)
    h_sum_right,
    intervalIntegral.integral_add (intervalIntegrable_left_of_continuousOn hc hT hcont) h_sum_left,
    intervalIntegral.integral_add (intervalIntegrable_top_of_continuousOn hc hT hcont) h_sum_top,
    intervalIntegral.integral_add (intervalIntegrable_bot_of_continuousOn hc hT hcont) h_sum_bot,
    intervalIntegral.integral_finsetSum fun p hp ↦ intervalIntegrable_pole_right (r p) (hP p hp),
    intervalIntegral.integral_finsetSum fun p hp ↦ intervalIntegrable_pole_left (r p) (hP p hp),
    intervalIntegral.integral_finsetSum fun p hp ↦ intervalIntegrable_pole_top (r p) (hP p hp),
    intervalIntegral.integral_finsetSum fun p hp ↦ intervalIntegrable_pole_bot (r p) (hP p hp)]
  simp only [mul_add, mul_sum, sum_add_distrib, sum_sub_distrib]
  ring

/-- **General Rectangle Residue Theorem (Holomorphic Remainder Form)**:
Let `P : Finset ℂ` be a finite set of poles strictly inside the rectangle `[c₁, c₂] × [-T, T]`
(`c₁ ≤ c₂`, `0 ≤ T`, `∀ p ∈ P, p ∈ openRect c₁ c₂ T`).
If `F : ℂ → ℂ` is continuous on `closedRect c₁ c₂ T`, complex-differentiable on
`openRect c₁ c₂ T \ s` for a countable set `s : Set ℂ`, and
`∀ z ∈ closedRect c₁ c₂ T \ P, M z = F z + ∑ p ∈ P, r p / (z - p)`, then
$$\operatorname{rectBoundaryIntegral} M\, c_1\, c_2\, T = 2\pi i \sum_{p \in P} r(p).$$ -/
theorem rectBoundaryIntegral_eq_sum_residues_off_countable {c₁ c₂ T : ℝ}
    (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {M F : ℂ → ℂ} {P : Finset ℂ} {r : ℂ → ℂ} {s : Set ℂ} (hs : s.Countable)
    (hP : ∀ p ∈ P, p ∈ openRect c₁ c₂ T)
    (hcont : ContinuousOn F (closedRect c₁ c₂ T))
    (hdiff : ∀ z ∈ openRect c₁ c₂ T \ s, DifferentiableAt ℂ F z)
    (hM : ∀ z ∈ closedRect c₁ c₂ T \ (P : Set ℂ), M z = F z + ∑ p ∈ P, r p / (z - p)) :
    rectBoundaryIntegral M c₁ c₂ T = 2 * π * I * ∑ p ∈ P, r p := by
  have hP_sub : (P : Set ℂ) ⊆ openRect c₁ c₂ T := fun p hp ↦ hP p (mem_coe.mp hp)
  have h_congr :
      rectBoundaryIntegral M c₁ c₂ T =
        rectBoundaryIntegral (fun z ↦ F z + ∑ p ∈ P, r p / (z - p)) c₁ c₂ T :=
    rectBoundaryIntegral_congr_of_eqOn_sdiff hc hT hP_sub hM
  rw [h_congr, rectBoundaryIntegral_add_sum_poles hc hT hcont P r hP,
    rectBoundaryIntegral_eq_zero_of_differentiable_on_off_countable hc hT hs hcont hdiff,
    zero_add, mul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  obtain ⟨⟨hre₁, hre₂⟩, ⟨him₁, him₂⟩⟩ := hP p hp
  exact rectBoundaryIntegral_div_sub_eq_two_pi_I_mul (r p) hre₁ hre₂ him₁ him₂

theorem inv_two_pi_I_mul_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * (I * z) = (2 * (Real.pi : ℂ))⁻¹ * z := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  rw [mul_inv, mul_assoc, inv_mul_cancel_left₀ hI]

theorem inv_two_pi_I_mul_two_pi_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * (2 * (Real.pi : ℂ) * I * z) = z := by
  have hne : 2 * (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact inv_mul_cancel_left₀ hne z

theorem right_vertical_integral_eq_rectBoundaryIntegral_add (f : ℂ → ℂ) (c₁ c₂ U : ℝ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (c₂ + t * I)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral f c₁ c₂ U +
        (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (c₁ + t * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c₁..c₂, f (σ + U * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c₁..c₂, f (σ - U * I)) := by
  have hrect : I * (∫ t in (-U)..U, f (c₂ + t * I)) =
      rectBoundaryIntegral f c₁ c₂ U +
        I * (∫ t in (-U)..U, f (c₁ + t * I)) +
        (∫ σ in c₁..c₂, f (σ + U * I)) -
        (∫ σ in c₁..c₂, f (σ - U * I)) := by
    unfold rectBoundaryIntegral
    ring
  have hmul := congrArg ((2 * (Real.pi : ℂ) * I)⁻¹ * ·) hrect
  rw [inv_two_pi_I_mul_I_mul] at hmul
  rw [hmul]
  simp only [mul_add, mul_sub, inv_two_pi_I_mul_I_mul]

theorem right_vertical_integral_two_eq_rectBoundaryIntegral_add (f : ℂ → ℂ) (a U : ℝ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (2 + (t : ℂ) * I)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral f a 2 U +
        (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + (t : ℂ) * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, f (σ + (U : ℂ) * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, f (σ - (U : ℂ) * I)) := by
  simpa using right_vertical_integral_eq_rectBoundaryIntegral_add f a 2 U

theorem norm_inv_two_pi_I_mul (z : ℂ) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * z‖ = (2 * Real.pi)⁻¹ * ‖z‖ := by
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le]
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, mul_one, h2pi]

theorem norm_inv_two_pi_mul (z : ℂ) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * z‖ = (2 * Real.pi)⁻¹ * ‖z‖ := by
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le]
  rw [norm_mul, norm_inv, h2pi]

theorem norm_contour_shift_remainder_le (f : ℂ → ℂ) (a c₂ U : ℝ) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + t * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ + U * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ - U * I))‖ ≤
      (2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, f (a + t * I)‖ +
        (2 * Real.pi)⁻¹ * ‖∫ σ in a..c₂, f (σ + U * I)‖ +
        (2 * Real.pi)⁻¹ * ‖∫ σ in a..c₂, f (σ - U * I)‖ := by
  calc
    ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + t * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ + U * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ - U * I))‖
      ≤ ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + t * I)) +
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ + U * I))‖ +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ - U * I))‖ := norm_sub_le _ _
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + t * I))‖ +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ + U * I))‖ +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ - U * I))‖ := by
        gcongr
        exact norm_add_le _ _
    _ = (2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, f (a + t * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..c₂, f (σ + U * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..c₂, f (σ - U * I)‖ := by
        rw [norm_inv_two_pi_mul, norm_inv_two_pi_I_mul, norm_inv_two_pi_I_mul]

/-- The sum of all principal parts of `smoothedPerronIntegrand x` in `{s | -1 / 2 < s.re ∧ |s.im| ≤
U}`. -/
noncomputable def perronPrincipalPartSum (x U : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ perronPolesUpTo U, perronResidue x p / (s - p)

theorem perronPrincipalPartSum_eq (x U : ℝ) (s : ℂ) :
    perronPrincipalPartSum x U s =
      resOne x / (s - 1) + resZero x / s +
        ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ / (s - ρ) := by
  unfold perronPrincipalPartSum perronPolesUpTo
  have h1_notMem : (1 : ℂ) ∉ insert (0 : ℂ) (nontrivialZetaZerosUpTo U) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨one_ne_zero, one_notMem_nontrivialZetaZerosUpTo U⟩
  have h0_notMem : (0 : ℂ) ∉ nontrivialZetaZerosUpTo U :=
    zero_notMem_nontrivialZetaZerosUpTo U
  rw [Finset.sum_insert h1_notMem, Finset.sum_insert h0_notMem,
    perronResidue_one, perronResidue_zero, sub_zero]
  have hsum : ∑ ρ ∈ nontrivialZetaZerosUpTo U, perronResidue x ρ / (s - ρ) =
      ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [perronResidue_of_mem_nontrivialZetaZerosUpTo x hρ]
  rw [hsum]
  ring

theorem smoothedPerronIntegrand_eq_regularized_add_principalParts (x U : ℝ) {s : ℂ}
    (hs : s ∉ perronPolesUpTo U) :
    smoothedPerronIntegrand x s =
      regularizedSmoothedPerron x U s + perronPrincipalPartSum x U s := by
  rw [regularizedSmoothedPerron_eq_of_notMem x U hs, perronPrincipalPartSum_eq]
  ring

theorem continuousOn_regularizedSmoothedPerron_closedRect
    {x U a b : ℝ} (hx : 0 < x) (ha : -1 / 2 < a) :
    ContinuousOn (regularizedSmoothedPerron x U) (closedRect a b U) := by
  intro s hs
  rw [mem_closedRect] at hs
  exact (differentiableAt_regularizedSmoothedPerron hx (by linarith [hs.1.1])
    (abs_le.mpr hs.2)).continuousAt.continuousWithinAt

/-- When `-1 / 2 < a < 0`, `0 < U`, and no zero in `nontrivialZetaZerosUpTo U` has `|ρ.im| = U`,
every pole in `perronPolesUpTo U` lies strictly inside `openRect a 2 U`. -/
theorem perronPolesUpTo_mem_openRect_of_neg
    {U a : ℝ} (hU : 0 < U) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    ∀ p ∈ perronPolesUpTo U, p ∈ openRect a 2 U := by
  intro p hp
  rw [mem_openRect]
  rcases mem_perronPolesUpTo.mp hp with rfl | rfl | hρ
  · simp only [one_re, one_im]
    exact ⟨⟨by linarith, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  · simp only [zero_re, zero_im]
    exact ⟨⟨ha_neg, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  · have hstrip := mem_criticalStrip_of_isNontrivialZetaZero (mem_nontrivialZetaZerosUpTo.mp hρ).1
    have him := abs_lt.mp (h_no_horiz p hρ)
    exact ⟨⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩, him⟩

theorem sum_perronPolesUpTo_perronResidue (x U : ℝ) :
    ∑ p ∈ perronPolesUpTo U, perronResidue x p =
      resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ := by
  unfold perronPolesUpTo
  have h1_notMem : (1 : ℂ) ∉ insert (0 : ℂ) (nontrivialZetaZerosUpTo U) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨one_ne_zero, one_notMem_nontrivialZetaZerosUpTo U⟩
  have h0_notMem : (0 : ℂ) ∉ nontrivialZetaZerosUpTo U :=
    zero_notMem_nontrivialZetaZerosUpTo U
  rw [Finset.sum_insert h1_notMem, Finset.sum_insert h0_notMem,
    perronResidue_one, perronResidue_zero]
  have hsum : ∑ ρ ∈ nontrivialZetaZerosUpTo U, perronResidue x ρ =
      ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ :=
    Finset.sum_congr rfl fun ρ hρ ↦ perronResidue_of_mem_nontrivialZetaZerosUpTo x hρ
  rw [hsum, add_assoc]

/-- **Exact Rectangle Residue Theorem for `smoothedPerronIntegrand` (`-1 / 2 < a < 0`)**:
For `0 < x`, `0 < U`, `-1 / 2 < a < 0`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U`,
$$\operatorname{rectBoundaryIntegral}(\text{smoothedPerronIntegrand } x)\, a\, 2\, U
  = 2\pi i \left(\text{resOne } x + \text{resZero } x + \sum_{\rho \in
  \text{nontrivialZetaZerosUpTo } U} \text{resZeroRho } x\, \rho\right).$$ -/
theorem rectBoundaryIntegral_smoothedPerronIntegrand_eq_residues_of_neg
    {x U a : ℝ} (hx : 0 < x) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    rectBoundaryIntegral (smoothedPerronIntegrand x) a 2 U =
      2 * (Real.pi : ℂ) * I *
        (resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ) := by
  have ha2 : a ≤ 2 := by linarith
  have hP := perronPolesUpTo_mem_openRect_of_neg hU ha_neg h_no_horiz
  have hres := rectBoundaryIntegral_eq_sum_residues_off_countable (c₁ := a) (c₂ := 2) (T := U)
    ha2 hU.le (M := smoothedPerronIntegrand x) (F := regularizedSmoothedPerron x U)
    (P := perronPolesUpTo U) (r := perronResidue x) countable_empty hP
    (continuousOn_regularizedSmoothedPerron_closedRect hx ha)
    (fun z hz ↦ differentiableAt_regularizedSmoothedPerron hx
      (by linarith [hz.1.1.1]) (abs_le.mpr ⟨hz.1.2.1.le, hz.1.2.2.le⟩))
    (fun z hz ↦ smoothedPerronIntegrand_eq_regularized_add_principalParts x U hz.2)
  rw [hres, sum_perronPolesUpTo_perronResidue]

/-- **Exact Contour Shift Identity for `-1 / 2 < a < 0`**:
For `0 < x`, `0 < U`, `-1 / 2 < a < 0`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U`:
$$(2\pi)^{-1} \int_{-U}^U \text{smoothedPerronIntegrand } x\, (2 + t I)\,dt
  = \text{resOne } x + \text{resZero } x + \sum_{\rho \in \text{nontrivialZetaZerosUpTo } U}
  \text{resZeroRho } x\, \rho
    + (2\pi)^{-1} \int_{-U}^U \text{smoothedPerronIntegrand } x\, (a + t I)\,dt
    + (2\pi i)^{-1} \left(\int_a^2 \text{smoothedPerronIntegrand } x\, (\sigma + U I)\,d\sigma
      - \int_a^2 \text{smoothedPerronIntegrand } x\, (\sigma - U I)\,d\sigma\right).$$ -/
theorem truncated_smoothedPerron_two_eq_residues_add_boundary_of_neg
    {x U a : ℝ} (hx : 0 < x) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) =
      (resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ) +
        ((2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (a + (t : ℂ) * I)) +
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, smoothedPerronIntegrand x (σ + (U : ℂ) * I)) -
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2,
            smoothedPerronIntegrand x (σ - (U : ℂ) * I))) := by
  rw [right_vertical_integral_two_eq_rectBoundaryIntegral_add (smoothedPerronIntegrand x) a U,
    rectBoundaryIntegral_smoothedPerronIntegrand_eq_residues_of_neg hx hU ha ha_neg h_no_horiz,
    inv_two_pi_I_mul_two_pi_I_mul]
  ring

theorem resOne_re (x : ℝ) : (resOne x).re = x ^ 2 / 2 := by
  unfold resOne
  have h : (x : ℂ) ^ 2 / 2 = ((x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, ofReal_re]

theorem neg_deriv_riemannZeta_div_zero :
    -deriv riemannZeta 0 / riemannZeta 0 = -((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  have hlog : Complex.log (2 * (Real.pi : ℂ)) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.ofReal_log Real.two_pi_pos.le]
  rw [hlog]
  ring

theorem resZero_eq (x : ℝ) :
    resZero x = -((x * Real.log (2 * Real.pi) : ℝ) : ℂ) := by
  unfold resZero
  rw [neg_deriv_riemannZeta_div_zero]
  push_cast
  ring

theorem resZero_re (x : ℝ) :
    (resZero x).re = -(x * Real.log (2 * Real.pi)) := by
  rw [resZero_eq, neg_re, ofReal_re]

theorem sum_resZeroRho_eq (x : ℝ) (S : Finset ℂ) :
    ∑ ρ ∈ S, resZeroRho x ρ =
      -(∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))) := by
  unfold resZeroRho smoothedPerronKernel
  simp only [neg_mul, sum_neg_distrib]

theorem abs_re_sub_le_norm (z w : ℂ) :
    |z.re - w.re| ≤ ‖z - w‖ := by
  rw [← sub_re]
  exact Complex.abs_re_le_norm (z - w)

theorem abs_psi1_sub_re_le_of_trunc_decomp {x tailBound : ℝ} {truncInt mainResidues
  contourRemainder : ℂ}
    (htail : ‖(psi1 x : ℂ) - truncInt‖ ≤ tailBound)
    (hdecomp : truncInt = mainResidues + contourRemainder) :
    |psi1 x - mainResidues.re| ≤ tailBound + ‖contourRemainder‖ := by
  calc
    |psi1 x - mainResidues.re|
      = |(psi1 x : ℂ).re - mainResidues.re| := by rw [ofReal_re]
    _ ≤ ‖(psi1 x : ℂ) - mainResidues‖ := abs_re_sub_le_norm _ _
    _ = ‖((psi1 x : ℂ) - truncInt) + contourRemainder‖ := by
        rw [hdecomp]
        ring_nf
    _ ≤ ‖(psi1 x : ℂ) - truncInt‖ + ‖contourRemainder‖ := norm_add_le _ _
    _ ≤ tailBound + ‖contourRemainder‖ := add_le_add_left htail _

/-- **Triangle Inequality Error Reduction for `-1 / 2 < a < 0` (including the $s = 0$ residue $-x
\log(2\pi)$)**:
For `1 ≤ x`, `0 < U`, `-1 / 2 < a < 0`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U`:
$$\left|\psi_1(x) - \frac{x^2}{2} + x \log(2\pi)
  - \left(-\sum_{\rho \in \text{nontrivialZetaZerosUpTo } U}
      \frac{(m_\rho : \mathbb{C}) (x : \mathbb{C})^{\rho + 1}}{\rho(\rho +
      1)}\right).\text{re}\right|$$
$$\le \frac{2 x^3}{\pi U}
  + \frac{1}{2\pi} \left\|\int_{-U}^U \text{smoothedPerronIntegrand}(x, a + t I)\,dt\right\|
  + \frac{1}{2\pi} \left\|\int_a^2 \text{smoothedPerronIntegrand}(x, \sigma + U I)\,d\sigma\right\|
  + \frac{1}{2\pi} \left\|\int_a^2 \text{smoothedPerronIntegrand}(x, \sigma - U
  I)\,d\sigma\right\|.$$ -/
theorem abs_psi1_sub_main_add_log_two_pi_sub_zeroSum_le_of_neg
    {x U a : ℝ} (hx : 1 ≤ x) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |psi1 x - x ^ 2 / 2 + x * Real.log (2 * Real.pi) -
      (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re| ≤
      2 * x ^ (3 : ℝ) / (Real.pi * U) +
        ((2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, smoothedPerronIntegrand x (a + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand x (σ + (U : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand x (σ - (U : ℂ) * I)‖) := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  have htail := norm_psi1_sub_truncated_smoothedPerron_two_le hx hU
  have hdecomp :=
    truncated_smoothedPerron_two_eq_residues_add_boundary_of_neg hx_pos hU ha ha_neg h_no_horiz
  have hbound := abs_psi1_sub_re_le_of_trunc_decomp htail hdecomp
  have hre : (resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ).re =
      x ^ 2 / 2 - x * Real.log (2 * Real.pi) +
        (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re := by
    rw [add_re, add_re, resOne_re, resZero_re, sum_resZeroRho_eq]
    ring
  have h_lhs : psi1 x - (resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U,
    resZeroRho x ρ).re =
      psi1 x - x ^ 2 / 2 + x * Real.log (2 * Real.pi) -
        (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re := by
    rw [hre]
    ring
  rw [← h_lhs]
  exact hbound.trans (add_le_add_right
    (norm_contour_shift_remainder_le (smoothedPerronIntegrand x) a 2 U) _)

/-- `Chebyshev.psi` is measurable, since it factors through `Nat.floor : ℝ → ℕ`. -/
theorem measurable_psi : Measurable Chebyshev.psi := by
  have heq : Chebyshev.psi =
    (fun n : ℕ ↦ ∑ k ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt k) ∘ Nat.floor := rfl
  rw [heq]
  exact measurable_from_nat.comp Nat.measurable_floor

/-- `Chebyshev.psi` is `IntervalIntegrable` on `[a, b]` for all `a b : ℝ`. -/
theorem intervalIntegrable_psi (a b : ℝ) :
    IntervalIntegrable Chebyshev.psi volume a b := by
  refine (intervalIntegrable_const (c := Chebyshev.psi (max a b))).mono_fun'
    measurable_psi.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Real.norm_of_nonneg (Chebyshev.psi_nonneg t)]
  have hle : t ≤ max a b := (uIoc_subset_uIcc ht).2
  exact Chebyshev.psi_mono hle

/-- For all `a b : ℝ`, `psi1 b - psi1 a = ∫ t in a..b, Chebyshev.psi t`. -/
theorem psi1_sub_psi1 (a b : ℝ) :
    psi1 b - psi1 a = ∫ t in a..b, Chebyshev.psi t := by
  unfold psi1
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_psi 1 a) (intervalIntegrable_psi a b)
  linarith

/-- If `a ≤ b`, then `(b - a) * Chebyshev.psi a ≤ psi1 b - psi1 a` and
`psi1 b - psi1 a ≤ (b - a) * Chebyshev.psi b`. -/
theorem mul_psi_le_psi1_sub_and_le {a b : ℝ} (hab : a ≤ b) :
    (b - a) * Chebyshev.psi a ≤ psi1 b - psi1 a ∧
      psi1 b - psi1 a ≤ (b - a) * Chebyshev.psi b := by
  rw [psi1_sub_psi1]
  constructor
  · calc
      (b - a) * Chebyshev.psi a = ∫ _ in a..b, Chebyshev.psi a := by
        simp [intervalIntegral.integral_const]
      _ ≤ ∫ t in a..b, Chebyshev.psi t :=
        intervalIntegral.integral_mono_on hab intervalIntegrable_const
          (intervalIntegrable_psi a b) fun t ht ↦ Chebyshev.psi_mono ht.1
  · calc
      (∫ t in a..b, Chebyshev.psi t) ≤ ∫ _ in a..b, Chebyshev.psi b :=
        intervalIntegral.integral_mono_on hab (intervalIntegrable_psi a b)
          intervalIntegrable_const fun t ht ↦ Chebyshev.psi_mono ht.2
      _ = (b - a) * Chebyshev.psi b := by
        simp [intervalIntegral.integral_const]

/-- **Upper Monotonicity Sandwich Lemma**:
For any `x : ℝ` and `0 < h`,
$$\psi(x) \le \frac{\psi_1(x + h) - \psi_1(x)}{h}.$$ -/
theorem psi_le_psi1_add_sub_div (x : ℝ) {h : ℝ} (hh : 0 < h) :
    Chebyshev.psi x ≤ (psi1 (x + h) - psi1 x) / h := by
  rw [le_div_iff₀ hh]
  have h1 := (mul_psi_le_psi1_sub_and_le (a := x) (b := x + h) (by linarith)).1
  linarith

/-- **Lower Monotonicity Sandwich Lemma**:
For any `x : ℝ` and `0 < h`,
$$\frac{\psi_1(x) - \psi_1(x - h)}{h} \le \psi(x).$$ -/
theorem psi1_sub_psi1_sub_div_le_psi (x : ℝ) {h : ℝ} (hh : 0 < h) :
    (psi1 x - psi1 (x - h)) / h ≤ Chebyshev.psi x := by
  rw [div_le_iff₀ hh]
  have h2 := (mul_psi_le_psi1_sub_and_le (a := x - h) (b := x) (by linarith)).2
  linarith

/-- The smoothed zero-sum term corresponding to the forward difference quotient of
`t ^ (ρ + 1) / (ρ * (ρ + 1))` over `[x, x + h]`:
$$\text{smoothedZeroTerm}(x, h, \rho)
  = \frac{(x + h)^{\rho + 1} - x^{\rho + 1}}{h \rho (\rho + 1)}.$$ -/
noncomputable def smoothedZeroTerm (x h : ℝ) (ρ : ℂ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)) / ((h : ℂ) * ρ * (ρ + 1))

/-- **Fundamental Theorem of Calculus for `∫_a^b t ^ ρ dt`**:
For any `a b : ℝ` and `ρ : ℂ` with `0 < ρ.re`,
$$\int_a^b t^\rho \, dt = \frac{b^{\rho + 1} - a^{\rho + 1}}{\rho + 1}.$$ -/
theorem integral_cpow_of_re_pos (a b : ℝ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    (∫ t : ℝ in a..b, (t : ℂ) ^ ρ) = ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ + 1) :=
  integral_cpow (Or.inl (by linarith))

/-- For `0 < ρ.re`, `smoothedZeroTerm x h ρ` equals `(∫ t in x..(x + h), (t : ℂ) ^ ρ) / (h * ρ)`. -/
theorem smoothedZeroTerm_eq_integral_div (x h : ℝ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    smoothedZeroTerm x h ρ = (∫ t : ℝ in x..(x + h), (t : ℂ) ^ ρ) / ((h : ℂ) * ρ) := by
  unfold smoothedZeroTerm
  rw [integral_cpow_of_re_pos x (x + h) hρ, div_div, mul_comm (ρ + 1)]

/-- **Low-Frequency Norm Bound for `smoothedZeroTerm` (`ρ.re = 1 / 2`)**:
If `0 < x`, `0 < h`, and `ρ.re = 1 / 2`, then
$$\|\text{smoothedZeroTerm}(x, h, \rho)\| \le \frac{\sqrt{x + h}}{\|\rho\|}.$$ -/
theorem norm_smoothedZeroTerm_le_sqrt_div_norm {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖smoothedZeroTerm x h ρ‖ ≤ Real.sqrt (x + h) / ‖ρ‖ := by
  have hρ_pos : 0 < ρ.re := by linarith
  rw [smoothedZeroTerm_eq_integral_div x h hρ_pos, norm_div, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hh.le]
  have hint_le : ‖∫ t : ℝ in x..(x + h), (t : ℂ) ^ ρ‖ ≤ Real.sqrt (x + h) * |x + h - x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [uIoc_of_le (by linarith)] at ht
    have ht_pos : 0 < t := hx.trans ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos, hre, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt ht.2
  have habs : |x + h - x| = h := by
    rw [add_sub_cancel_left, abs_of_pos hh]
  rw [habs] at hint_le
  calc
    ‖∫ t : ℝ in x..(x + h), (t : ℂ) ^ ρ‖ / (h * ‖ρ‖)
      ≤ (Real.sqrt (x + h) * h) / (h * ‖ρ‖) :=
        div_le_div_of_nonneg_right hint_le (mul_nonneg hh.le (norm_nonneg ρ))
    _ = Real.sqrt (x + h) / ‖ρ‖ := by
        rw [mul_comm (Real.sqrt (x + h)) h, mul_div_mul_left _ _ hh.ne']

/-- For any complex number `ρ`, `|ρ.im| ^ 2 ≤ ‖ρ * (ρ + 1)‖`. -/
theorem sq_abs_im_le_norm_mul_add_one (ρ : ℂ) :
    |ρ.im| ^ 2 ≤ ‖ρ * (ρ + 1)‖ := by
  rw [sq, norm_mul]
  have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have h2 : |ρ.im| ≤ ‖ρ + 1‖ := by
    simpa using Complex.abs_im_le_norm (ρ + 1)
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

end ConjectureMachines.Semantics.Riemann.WeightedStieltjes
