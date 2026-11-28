/- GID: D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact scalar minimum for the two-mode Wu orientation reduction. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases

/-!
Exact scalar minimisation for the two-mode Wu orientation reduction.

The variables `Xᵢ` and `Yᵢ` are squared lengths.  The first family has
total mass one and the second has total mass at most one.  The theorem below
identifies this product of simplexes with the union of the two single-mode
axes.  The proof is elementary and keeps the signs of the linear terms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace WuTwoLevelOrientationMinimum

def axisQuadratic (C A b u : ℝ) : ℝ :=
  C + A / 2 * (1 + u ^ 2) - b * u

def productQuadratic (C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) : ℝ :=
  C + (A₁ / 2) * (X₁ + Y₁) - b₁ * Real.sqrt (X₁ * Y₁) +
    (A₂ / 2) * (X₂ + Y₂) - b₂ * Real.sqrt (X₂ * Y₂)

def axisArg (A b : ℝ) : ℝ :=
  if A = 0 then 1 else if b ≤ A then b / A else 1

def axisMinimum (C A b : ℝ) : ℝ := axisQuadratic C A b (axisArg A b)

def twoModeMinimum (C A₁ A₂ b₁ b₂ : ℝ) : ℝ :=
  min (axisMinimum C A₁ b₁) (axisMinimum C A₂ b₂)

private theorem axisArg_mem {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    0 ≤ axisArg A b ∧ axisArg A b ≤ 1 := by
  by_cases hA0 : A = 0
  · simp [axisArg, hA0]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    by_cases hba : b ≤ A
    · simp only [axisArg, hA0, hba]
      constructor
      · exact div_nonneg hb hApos.le
      · apply (div_le_iff₀ hApos).2
        simpa only [one_mul] using hba
    · simp [axisArg, hA0, hba]

private theorem axisQuadratic_lower {C A b u : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    axisMinimum C A b ≤ axisQuadratic C A b u := by
  by_cases hA0 : A = 0
  · have hbu := mul_le_mul_of_nonneg_left hu₁ hb
    simpa [axisMinimum, axisArg, axisQuadratic, hA0] using sub_le_sub_left hbu C
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    by_cases hba : b ≤ A
    · have harg : axisArg A b = b / A := by simp [axisArg, hA0, hba]
      simp only [axisMinimum, harg, axisQuadratic]
      have hs : 0 ≤ A / 2 * (u - b / A) ^ 2 := by positivity
      have hid :
          A / 2 * (1 + u ^ 2) - b * u -
              (A / 2 * (1 + (b / A) ^ 2) - b * (b / A)) =
            A / 2 * (u - b / A) ^ 2 := by
        field_simp [hA0]
        ring
      linarith only [hs, hid]
    · have harg : axisArg A b = 1 := by simp [axisArg, hA0, hba]
      simp only [axisMinimum, harg, axisQuadratic]
      have hfac : 0 ≤ (1 - u) * (b - A * (1 + u) / 2) := by
        apply mul_nonneg (sub_nonneg.mpr hu₁)
        have hsum : 1 + u ≤ (2 : ℝ) := by linarith
        have hprod : A * (1 + u) ≤ A * 2 :=
          mul_le_mul_of_nonneg_left hsum hA
        have hhalf : A * (1 + u) / 2 ≤ A := by linarith
        have hnot : A < b := lt_of_not_ge hba
        linarith
      have hid :
          A / 2 * (1 + u ^ 2) - b * u - (A - b) =
            (1 - u) * (b - A * (1 + u) / 2) := by ring
      linarith only [hfac, hid]

private theorem two_root_cauchy
    {X₁ X₂ Y₁ Y₂ : ℝ} (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) (hX : X₁ + X₂ = 1) (hY : Y₁ + Y₂ ≤ 1) :
    Real.sqrt (X₁ * Y₁) + Real.sqrt (X₂ * Y₂) ≤ 1 := by
  let r₁ := Real.sqrt (X₁ * Y₁)
  let r₂ := Real.sqrt (X₂ * Y₂)
  let p := Real.sqrt (X₁ * Y₂)
  let q := Real.sqrt (X₂ * Y₁)
  have hr₁ : 0 ≤ r₁ := Real.sqrt_nonneg _
  have hr₂ : 0 ≤ r₂ := Real.sqrt_nonneg _
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hr₁sq : r₁ ^ 2 = X₁ * Y₁ := by
    dsimp [r₁]
    exact Real.sq_sqrt (mul_nonneg hX₁ hY₁)
  have hr₂sq : r₂ ^ 2 = X₂ * Y₂ := by
    dsimp [r₂]
    exact Real.sq_sqrt (mul_nonneg hX₂ hY₂)
  have hpsq : p ^ 2 = X₁ * Y₂ := by
    dsimp [p]
    exact Real.sq_sqrt (mul_nonneg hX₁ hY₂)
  have hqsq : q ^ 2 = X₂ * Y₁ := by
    dsimp [q]
    exact Real.sq_sqrt (mul_nonneg hX₂ hY₁)
  have hpq : p * q = r₁ * r₂ := by
    have hs : (p * q) ^ 2 = (r₁ * r₂) ^ 2 := by
      simp only [mul_pow, hpsq, hqsq, hr₁sq, hr₂sq]
      ring
    exact (sq_eq_sq₀ (mul_nonneg hp hq) (mul_nonneg hr₁ hr₂)).1 hs
  have hcross : 2 * r₁ * r₂ ≤ X₁ * Y₂ + X₂ * Y₁ := by
    have hs := sq_nonneg (p - q)
    nlinarith [hpsq, hqsq, hpq]
  have hprod : (r₁ + r₂) ^ 2 ≤ (X₁ + X₂) * (Y₁ + Y₂) := by
    nlinarith [hr₁sq, hr₂sq, hcross]
  have hsq : (r₁ + r₂) ^ 2 ≤ 1 := by nlinarith [hprod]
  dsimp [r₁, r₂] at hr₁ hr₂ ⊢
  nlinarith [hsq]

private theorem product_nonneg_of_axes_nonneg_posC
    {C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ}
    (hC : 0 ≤ C) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hX : X₁ + X₂ = 1) (hY : Y₁ + Y₂ ≤ 1)
    (ha₁ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ axisQuadratic C A₁ b₁ u)
    (ha₂ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ axisQuadratic C A₂ b₂ u) :
    0 ≤ productQuadratic C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂ := by
  let r₁ := Real.sqrt (X₁ * Y₁)
  let r₂ := Real.sqrt (X₂ * Y₂)
  let sx₁ := Real.sqrt X₁
  let sx₂ := Real.sqrt X₂
  let sy₁ := Real.sqrt Y₁
  let sy₂ := Real.sqrt Y₂
  have hr₁ : 0 ≤ r₁ := Real.sqrt_nonneg _
  have hr₂ : 0 ≤ r₂ := Real.sqrt_nonneg _
  have hroot : r₁ + r₂ ≤ 1 := by
    dsimp [r₁, r₂]
    exact two_root_cauchy hX₁ hX₂ hY₁ hY₂ hX hY
  have hba₁ : b₁ ≤ C + A₁ := by
    have h := ha₁ 1 zero_le_one le_rfl
    dsimp [axisQuadratic] at h
    linarith
  have hba₂ : b₂ ≤ C + A₂ := by
    have h := ha₂ 1 zero_le_one le_rfl
    dsimp [axisQuadratic] at h
    linarith
  have hbterm₁ : b₁ * r₁ ≤ (C + A₁) * r₁ :=
    mul_le_mul_of_nonneg_right hba₁ hr₁
  have hbterm₂ : b₂ * r₂ ≤ (C + A₂) * r₂ :=
    mul_le_mul_of_nonneg_right hba₂ hr₂
  have hsx₁ : sx₁ ^ 2 = X₁ := by
    dsimp [sx₁]
    exact Real.sq_sqrt hX₁
  have hsx₂ : sx₂ ^ 2 = X₂ := by
    dsimp [sx₂]
    exact Real.sq_sqrt hX₂
  have hsy₁ : sy₁ ^ 2 = Y₁ := by
    dsimp [sy₁]
    exact Real.sq_sqrt hY₁
  have hsy₂ : sy₂ ^ 2 = Y₂ := by
    dsimp [sy₂]
    exact Real.sq_sqrt hY₂
  have hrprod₁ : r₁ = sx₁ * sy₁ := by
    dsimp [r₁, sx₁, sy₁]
    exact Real.sqrt_mul hX₁ Y₁
  have hrprod₂ : r₂ = sx₂ * sy₂ := by
    dsimp [r₂, sx₂, sy₂]
    exact Real.sqrt_mul hX₂ Y₂
  have hsquare₁ : (sx₁ - sy₁) ^ 2 = X₁ + Y₁ - 2 * r₁ := by
    rw [hrprod₁]
    nlinarith [hsx₁, hsy₁]
  have hsquare₂ : (sx₂ - sy₂) ^ 2 = X₂ + Y₂ - 2 * r₂ := by
    rw [hrprod₂]
    nlinarith [hsx₂, hsy₂]
  have hdecomp :
      C + A₁ / 2 * (X₁ + Y₁) - (C + A₁) * r₁ +
          (A₂ / 2) * (X₂ + Y₂) - (C + A₂) * r₂ =
        C * (1 - r₁ - r₂) + A₁ / 2 * (sx₁ - sy₁) ^ 2 +
          A₂ / 2 * (sx₂ - sy₂) ^ 2 := by
    nlinarith [hsquare₁, hsquare₂, hX]
  have hnonneg :
      0 ≤ C * (1 - r₁ - r₂) + A₁ / 2 * (sx₁ - sy₁) ^ 2 +
        A₂ / 2 * (sx₂ - sy₂) ^ 2 := by
    have h₀ : 0 ≤ C * (1 - r₁ - r₂) :=
      mul_nonneg hC (by linarith only [hroot])
    exact add_nonneg (add_nonneg h₀
      (mul_nonneg (by positivity) (sq_nonneg _)))
      (mul_nonneg (by positivity) (sq_nonneg _))
  change 0 ≤ C + A₁ / 2 * (X₁ + Y₁) - b₁ * r₁ +
    A₂ / 2 * (X₂ + Y₂) - b₂ * r₂
  nlinarith [hdecomp, hbterm₁, hbterm₂, hnonneg]

private theorem product_nonneg_of_axes_nonneg_negC
    {C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ}
    (hC : C < 0)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hX : X₁ + X₂ = 1)
    (ha₁ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ axisQuadratic C A₁ b₁ u)
    (ha₂ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ axisQuadratic C A₂ b₂ u) :
    0 ≤ productQuadratic C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂ := by
  have hA₁pos : 0 < A₁ := by
    have h := ha₁ 1 zero_le_one le_rfl
    dsimp [axisQuadratic] at h
    have hlt : b₁ < A₁ := by linarith
    exact lt_of_le_of_lt hb₁ hlt
  have hA₂pos : 0 < A₂ := by
    have h := ha₂ 1 zero_le_one le_rfl
    dsimp [axisQuadratic] at h
    have hlt : b₂ < A₂ := by linarith
    exact lt_of_le_of_lt hb₂ hlt
  have htest₁ : 0 ≤ axisQuadratic C A₁ b₁ (b₁ / A₁) := by
    apply ha₁
    · exact div_nonneg hb₁ hA₁pos.le
    · exact (div_le_iff₀ hA₁pos).2 (by
        have h := ha₁ 1 zero_le_one le_rfl
        dsimp [axisQuadratic] at h
        linarith)
  have htest₂ : 0 ≤ axisQuadratic C A₂ b₂ (b₂ / A₂) := by
    apply ha₂
    · exact div_nonneg hb₂ hA₂pos.le
    · exact (div_le_iff₀ hA₂pos).2 (by
        have h := ha₂ 1 zero_le_one le_rfl
        dsimp [axisQuadratic] at h
        linarith)
  have hcoef₁ : 0 ≤ C + A₁ / 2 - b₁ ^ 2 / (2 * A₁) := by
    have hid : axisQuadratic C A₁ b₁ (b₁ / A₁) =
        C + A₁ / 2 - b₁ ^ 2 / (2 * A₁) := by
      dsimp [axisQuadratic]
      field_simp [ne_of_gt hA₁pos]
      ring
    rw [← hid]
    exact htest₁
  have hcoef₂ : 0 ≤ C + A₂ / 2 - b₂ ^ 2 / (2 * A₂) := by
    have hid : axisQuadratic C A₂ b₂ (b₂ / A₂) =
        C + A₂ / 2 - b₂ ^ 2 / (2 * A₂) := by
      dsimp [axisQuadratic]
      field_simp [ne_of_gt hA₂pos]
      ring
    rw [← hid]
    exact htest₂
  let sx₁ := Real.sqrt X₁
  let sx₂ := Real.sqrt X₂
  let sy₁ := Real.sqrt Y₁
  let sy₂ := Real.sqrt Y₂
  have hsx₁ : 0 ≤ sx₁ := Real.sqrt_nonneg _
  have hsx₂ : 0 ≤ sx₂ := Real.sqrt_nonneg _
  have hsy₁ : 0 ≤ sy₁ := Real.sqrt_nonneg _
  have hsy₂ : 0 ≤ sy₂ := Real.sqrt_nonneg _
  have hsx₁sq : sx₁ ^ 2 = X₁ := by
    dsimp [sx₁]
    exact Real.sq_sqrt hX₁
  have hsx₂sq : sx₂ ^ 2 = X₂ := by
    dsimp [sx₂]
    exact Real.sq_sqrt hX₂
  have hsy₁sq : sy₁ ^ 2 = Y₁ := by
    dsimp [sy₁]
    exact Real.sq_sqrt hY₁
  have hsy₂sq : sy₂ ^ 2 = Y₂ := by
    dsimp [sy₂]
    exact Real.sq_sqrt hY₂
  have hprod₁ : Real.sqrt (X₁ * Y₁) = sx₁ * sy₁ := by
    dsimp [sx₁, sy₁]
    exact Real.sqrt_mul hX₁ Y₁
  have hprod₂ : Real.sqrt (X₂ * Y₂) = sx₂ * sy₂ := by
    dsimp [sx₂, sy₂]
    exact Real.sqrt_mul hX₂ Y₂
  have hsq₁ :
      0 ≤ A₁ / 2 * (X₁ + Y₁) - b₁ * (sx₁ * sy₁) -
        X₁ * (A₁ / 2 - b₁ ^ 2 / (2 * A₁)) := by
    have hid :
        A₁ / 2 * (X₁ + Y₁) - b₁ * (sx₁ * sy₁) -
            X₁ * (A₁ / 2 - b₁ ^ 2 / (2 * A₁)) =
          A₁ / 2 * (sy₁ - (b₁ / A₁) * sx₁) ^ 2 := by
      field_simp [ne_of_gt hA₁pos]
      nlinarith [hsx₁sq, hsy₁sq]
    rw [hid]
    positivity
  have hsq₂ :
      0 ≤ A₂ / 2 * (X₂ + Y₂) - b₂ * (sx₂ * sy₂) -
        X₂ * (A₂ / 2 - b₂ ^ 2 / (2 * A₂)) := by
    have hid :
        A₂ / 2 * (X₂ + Y₂) - b₂ * (sx₂ * sy₂) -
            X₂ * (A₂ / 2 - b₂ ^ 2 / (2 * A₂)) =
          A₂ / 2 * (sy₂ - (b₂ / A₂) * sx₂) ^ 2 := by
      field_simp [ne_of_gt hA₂pos]
      nlinarith [hsx₂sq, hsy₂sq]
    rw [hid]
    positivity
  dsimp [productQuadratic]
  rw [hprod₁, hprod₂]
  nlinarith [hsq₁, hsq₂, hcoef₁, hcoef₂, hX]

private theorem product_nonneg_of_axes_nonneg
    {C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hX : X₁ + X₂ = 1) (hY : Y₁ + Y₂ ≤ 1)
    (ha₁ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ axisQuadratic C A₁ b₁ u)
    (ha₂ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ axisQuadratic C A₂ b₂ u) :
    0 ≤ productQuadratic C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂ := by
  by_cases hC : 0 ≤ C
  · exact product_nonneg_of_axes_nonneg_posC hC hA₁ hA₂ hb₁ hb₂ hX₁ hX₂ hY₁ hY₂ hX hY ha₁ ha₂
  · exact product_nonneg_of_axes_nonneg_negC (lt_of_not_ge hC) hb₁ hb₂
      hX₁ hX₂ hY₁ hY₂ hX ha₁ ha₂

theorem axis_minimum_lower {C A b u : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    axisMinimum C A b ≤ axisQuadratic C A b u :=
  axisQuadratic_lower hA hb hu₀ hu₁

theorem axis_minimum_formula {C A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    axisMinimum C A b =
      if A = 0 then C - b else
      if b ≤ A then C + A / 2 - b ^ 2 / (2 * A) else C + A - b := by
  by_cases hA0 : A = 0
  · simp [axisMinimum, axisArg, axisQuadratic, hA0]
  · by_cases hba : b ≤ A
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      simp only [axisMinimum, axisArg, hA0, hba]
      dsimp [axisQuadratic]
      field_simp [ne_of_gt hApos]
      ring
    · simp [axisMinimum, axisArg, axisQuadratic, hA0, hba] <;> ring

theorem twoMode_exact_minimum
    {C A₁ A₂ b₁ b₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    (∀ X₁ X₂ Y₁ Y₂ : ℝ,
      0 ≤ X₁ → 0 ≤ X₂ → 0 ≤ Y₁ → 0 ≤ Y₂ → X₁ + X₂ = 1 → Y₁ + Y₂ ≤ 1 →
      twoModeMinimum C A₁ A₂ b₁ b₂ ≤
        productQuadratic C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂) ∧
    (∃ X₁ X₂ Y₁ Y₂ : ℝ,
      0 ≤ X₁ ∧ 0 ≤ X₂ ∧ 0 ≤ Y₁ ∧ 0 ≤ Y₂ ∧ X₁ + X₂ = 1 ∧ Y₁ + Y₂ ≤ 1 ∧
      productQuadratic C A₁ A₂ b₁ b₂ X₁ X₂ Y₁ Y₂ =
        twoModeMinimum C A₁ A₂ b₁ b₂) ∧
    (∀ i : Fin 2, ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      twoModeMinimum C A₁ A₂ b₁ b₂ ≤
        axisQuadratic C (![A₁, A₂] i) (![b₁, b₂] i) u) ∧
    (∃ i : Fin 2, ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      axisQuadratic C (![A₁, A₂] i) (![b₁, b₂] i) u =
        twoModeMinimum C A₁ A₂ b₁ b₂) := by
  have haxis₁ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      axisMinimum C A₁ b₁ ≤ axisQuadratic C A₁ b₁ u :=
    fun u hu₀ hu₁ => axisQuadratic_lower hA₁ hb₁ hu₀ hu₁
  have haxis₂ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      axisMinimum C A₂ b₂ ≤ axisQuadratic C A₂ b₂ u :=
    fun u hu₀ hu₁ => axisQuadratic_lower hA₂ hb₂ hu₀ hu₁
  have hnonneg₁ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      0 ≤ axisQuadratic (C - twoModeMinimum C A₁ A₂ b₁ b₂) A₁ b₁ u := by
    intro u hu₀ hu₁
    have hm : twoModeMinimum C A₁ A₂ b₁ b₂ ≤ axisMinimum C A₁ b₁ := min_le_left _ _
    have h := haxis₁ u hu₀ hu₁
    dsimp only [axisQuadratic] at h ⊢
    linarith only [hm, h]
  have hnonneg₂ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      0 ≤ axisQuadratic (C - twoModeMinimum C A₁ A₂ b₁ b₂) A₂ b₂ u := by
    intro u hu₀ hu₁
    have hm : twoModeMinimum C A₁ A₂ b₁ b₂ ≤ axisMinimum C A₂ b₂ := min_le_right _ _
    have h := haxis₂ u hu₀ hu₁
    dsimp only [axisQuadratic] at h ⊢
    linarith only [hm, h]
  constructor
  · intro X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hX hY
    have h := product_nonneg_of_axes_nonneg hA₁ hA₂ hb₁ hb₂ hX₁ hX₂ hY₁ hY₂ hX hY
      hnonneg₁ hnonneg₂
    dsimp only [productQuadratic] at h ⊢
    linarith only [h]
  constructor
  · by_cases hm : axisMinimum C A₁ b₁ ≤ axisMinimum C A₂ b₂
    · have hu₀ := (axisArg_mem hA₁ hb₁).1
      have hu₁ := (axisArg_mem hA₁ hb₁).2
      have hu₂ : (axisArg A₁ b₁) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hu₀ (sub_nonneg.mpr hu₁)]
      refine ⟨1, 0, (axisArg A₁ b₁) ^ 2, 0, by positivity, by positivity,
        sq_nonneg _, by positivity, by ring, by linarith, ?_⟩
      rw [twoModeMinimum, min_eq_left hm]
      simp [productQuadratic, axisMinimum, axisQuadratic, Real.sqrt_sq hu₀]
    · have hm' : axisMinimum C A₂ b₂ ≤ axisMinimum C A₁ b₁ := le_of_not_ge hm
      have hu₀ := (axisArg_mem hA₂ hb₂).1
      have hu₁ := (axisArg_mem hA₂ hb₂).2
      have hu₂ : (axisArg A₂ b₂) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hu₀ (sub_nonneg.mpr hu₁)]
      refine ⟨0, 1, 0, (axisArg A₂ b₂) ^ 2, by positivity, by positivity,
        by positivity, sq_nonneg _, by ring, by linarith, ?_⟩
      rw [twoModeMinimum, min_eq_right hm']
      simp [productQuadratic, axisMinimum, axisQuadratic, Real.sqrt_sq hu₀]
  constructor
  · intro i u hu₀ hu₁
    fin_cases i
    · exact (min_le_left _ _).trans (haxis₁ u hu₀ hu₁)
    · exact (min_le_right _ _).trans (haxis₂ u hu₀ hu₁)
  · by_cases hm : axisMinimum C A₁ b₁ ≤ axisMinimum C A₂ b₂
    · refine ⟨0, axisArg A₁ b₁, (axisArg_mem hA₁ hb₁).1, (axisArg_mem hA₁ hb₁).2, ?_⟩
      change axisMinimum C A₁ b₁ = twoModeMinimum C A₁ A₂ b₁ b₂
      exact (min_eq_left hm).symm
    · have hm' : axisMinimum C A₂ b₂ ≤ axisMinimum C A₁ b₁ := le_of_not_ge hm
      refine ⟨1, axisArg A₂ b₂, (axisArg_mem hA₂ hb₂).1, (axisArg_mem hA₂ hb₂).2, ?_⟩
      change axisMinimum C A₂ b₂ = twoModeMinimum C A₁ A₂ b₁ b₂
      exact (min_eq_right hm').symm

/- The determinant estimate used by the real two-plane version. -/
theorem real_two_plane_determinant_bound
    {u₁ u₂ v₁ v₂ : ℝ} :
    (u₁ * v₂ - u₂ * v₁) ^ 2 ≤
      (u₁ ^ 2 + u₂ ^ 2) * (v₁ ^ 2 + v₂ ^ 2) := by
  nlinarith [sq_nonneg (u₁ * v₁ + u₂ * v₂)]

/- The two physical block weights occurring in the rank-two reduction.  This
   bound records the determinant occupations before any claim that the full
   six-coordinate orientation minimum is attained in these blocks. -/
theorem real_two_plane_physical_weight_bound
    {A₁ A₂ u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) :
    2 * (A₁ * |u₁ * v₂ - u₂ * v₁| + A₂ * |u₃ * v₄ - u₄ * v₃|) ≤
      A₁ * (u₁ ^ 2 + u₂ ^ 2 + v₁ ^ 2 + v₂ ^ 2) +
        A₂ * (u₃ ^ 2 + u₄ ^ 2 + v₃ ^ 2 + v₄ ^ 2) := by
  have hblock₁ : 2 * |u₁ * v₂ - u₂ * v₁| ≤
      u₁ ^ 2 + u₂ ^ 2 + v₁ ^ 2 + v₂ ^ 2 := by
    by_cases hd : 0 ≤ u₁ * v₂ - u₂ * v₁
    · rw [abs_of_nonneg hd]
      have hdet := real_two_plane_determinant_bound (u₁ := u₁) (u₂ := u₂)
        (v₁ := v₁) (v₂ := v₂)
      nlinarith [sq_nonneg (u₁ ^ 2 + u₂ ^ 2 - (v₁ ^ 2 + v₂ ^ 2))]
    · have hd' : u₁ * v₂ - u₂ * v₁ ≤ 0 := le_of_not_ge hd
      rw [abs_of_nonpos hd']
      have hdet := real_two_plane_determinant_bound (u₁ := u₁) (u₂ := u₂)
        (v₁ := v₁) (v₂ := v₂)
      nlinarith [sq_nonneg (u₁ ^ 2 + u₂ ^ 2 - (v₁ ^ 2 + v₂ ^ 2))]
  have hblock₂ : 2 * |u₃ * v₄ - u₄ * v₃| ≤
      u₃ ^ 2 + u₄ ^ 2 + v₃ ^ 2 + v₄ ^ 2 := by
    by_cases hd : 0 ≤ u₃ * v₄ - u₄ * v₃
    · rw [abs_of_nonneg hd]
      have hdet := real_two_plane_determinant_bound (u₁ := u₃) (u₂ := u₄)
        (v₁ := v₃) (v₂ := v₄)
      nlinarith [sq_nonneg (u₃ ^ 2 + u₄ ^ 2 - (v₃ ^ 2 + v₄ ^ 2))]
    · have hd' : u₃ * v₄ - u₄ * v₃ ≤ 0 := le_of_not_ge hd
      rw [abs_of_nonpos hd']
      have hdet := real_two_plane_determinant_bound (u₁ := u₃) (u₂ := u₄)
        (v₁ := v₃) (v₂ := v₄)
      nlinarith [sq_nonneg (u₃ ^ 2 + u₄ ^ 2 - (v₃ ^ 2 + v₄ ^ 2))]
  have h₁ := mul_le_mul_of_nonneg_left hblock₁ hA₁
  have h₂ := mul_le_mul_of_nonneg_left hblock₂ hA₂
  nlinarith

end WuTwoLevelOrientationMinimum
