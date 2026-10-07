/- GID: D5/S3/Arith/Lattices/Klartag/Completion/WindowR2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/WindowR2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.WindowR
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.WindowR2

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open scoped ENNReal NNReal

/-- The weakest eigenvalue bound the far band can use: `a0C n − 1/2`. -/
noncomputable def mR2 (n : ℕ) : ℝ := a0C n - 1 / 2

/-- **`window_small` at the generic reach**, now `le_refl`. -/
theorem mR2_ge (n : ℕ) : a0C n - 1 / 2 ≤ mR2 n := le_refl _

/-- `a0C n ≤ 1 + 3/n`. -/
theorem a0C_le_one_add {n : ℕ} (hn : 2073600 ≤ n) : a0C n ≤ 1 + 3 / (n : ℝ) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2073600 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  rw [a0C, inv_pow, ← one_div, div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [hn0, hnR]

theorem mR2_pos {n : ℕ} (hn : 2073600 ≤ n) : 0 < mR2 n := by
  have h1 : (1 : ℝ) ≤ a0C n := a0C_ge_one (by omega)
  rw [mR2]; linarith

theorem mR2_lt_one {n : ℕ} (hn : 2073600 ≤ n) : mR2 n < 1 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h3 : 3 / (n : ℝ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
  have h := a0C_le_one_add hn
  rw [mR2]; linarith

/-- **The band closes at `windowR2` for every admissible contact threshold.**  This is the point
of the module: `c₃` may change without the window moving. -/
theorem mAt_ge_mR2 {n : ℕ} (hn : 2073600 ≤ n) {c₃ : ℝ} (_hc₃0 : 0 ≤ c₃)
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    mR2 n ≤ GoodPathBounds.mAt n c₃ := by
  rw [mR2, GoodPathBounds.mAt]
  linarith [WindowR.r0Adopted_le hn]

/-- `YR2 n·√T = a0C n − mR2 n = 1/2`, identically in `t`. -/
noncomputable def YR2 (n : ℕ) : ℝ := (a0C n - mR2 n) / Real.sqrt (ChainDrift.horizon n)

/-- The generic reach window's numerator: `windowR2 α n = reachNum2 n/α + √n/2` by `rfl`. -/
noncomputable def reachNum2 (n : ℕ) : ℝ :=
  subst (a0C n) (Real.sqrt (ChainDrift.horizon n)) (YR2 n)

/-- **The generic reach window.** -/
noncomputable def windowR2 (α : ℝ) (n : ℕ) : ℝ :=
  radiusOf (a0C n) α (Real.sqrt n / 2) (ChainDrift.horizon n) (YR2 n)

theorem windowR2_eq (α : ℝ) (n : ℕ) : windowR2 α n = reachNum2 n / α + Real.sqrt n / 2 := rfl

theorem sqrtT_mul_YR2 {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt (ChainDrift.horizon n) * YR2 n = a0C n - mR2 n := by
  rw [YR2, mul_div_cancel₀ _ (ne_of_gt (WindowR.sqrtT_pos hn))]

/-- **`reachNum2 = 1/√(mR2)`.** -/
theorem reachNum2_eq {n : ℕ} (hn : 2073600 ≤ n) : reachNum2 n = 1 / Real.sqrt (mR2 n) := by
  have h := sqrtT_mul_YR2 (n := n) (by omega)
  rw [reachNum2, subst, h]
  have : a0C n - (a0C n - mR2 n) = mR2 n := by ring
  rw [this, one_div]

theorem one_lt_reachNum2 {n : ℕ} (hn : 2073600 ≤ n) : 1 < reachNum2 n := by
  rw [reachNum2_eq hn]
  have hm : 0 < mR2 n := mR2_pos hn
  have hlt : mR2 n < 1 := mR2_lt_one hn
  have hs : Real.sqrt (mR2 n) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt hm.le hlt
  have hs0 : 0 < Real.sqrt (mR2 n) := Real.sqrt_pos.2 hm
  rw [lt_div_iff₀ hs0]; linarith

/-- **`window_lt_p` at the generic reach**: `2·reachNum2 n ≤ α·p` and `α·√n ≤ 1` give
`windowR2 α n < p`.  `reachNum2 ≈ √2`, so the hypothesis is `2.829 ≤ α·p`. -/
theorem windowR2_lt_p {α p : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (h2 : 2 * reachNum2 n ≤ α * p) (hsn : α * Real.sqrt n ≤ 1) : windowR2 α n < p := by
  have h1 : (1 : ℝ) < reachNum2 n := one_lt_reachNum2 hn
  have hαp : (1 : ℝ) < α * p := by linarith
  have hrn : reachNum2 n / α ≤ p / 2 := by
    rw [div_le_iff₀ hα]; nlinarith
  have hsq : Real.sqrt n / 2 ≤ 1 / (2 * α) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hhalf : 1 / (2 * α) < p / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [windowR2_eq]
  linarith

end D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
