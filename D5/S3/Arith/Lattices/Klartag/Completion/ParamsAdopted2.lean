/- GID: D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.Discharge
import D5.S3.Arith.Lattices.Klartag.State.StepGlue

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.ParamsAdopted2

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

noncomputable section

/-- `N = ⌈16 n⁷ log n⌉` — the adopted number of steps at `h = n⁻⁹`. -/
noncomputable def numStepsAdopted2 (n : ℕ) : ℕ := ChainDrift.numSteps n 7

/-- `h = T / N ≤ n⁻⁹` — the adopted step size. -/
noncomputable def stepSizeAdopted2 (n : ℕ) : ℝ := ChainDrift.stepSize n 7

/-- The horizon is hit exactly: `N · h = T`. -/
theorem numStepsAdopted2_mul_stepSizeAdopted2 {n : ℕ} (hn : 3 ≤ n) :
    (numStepsAdopted2 n : ℝ) * stepSizeAdopted2 n = ChainDrift.horizon n := by
  rw [numStepsAdopted2, stepSizeAdopted2, ChainDrift.stepSize,
    mul_div_cancel₀ _ (ne_of_gt (ChainDrift.numSteps_pos hn))]

theorem stepSizeAdopted2_le {n : ℕ} (hn : 3 ≤ n) : stepSizeAdopted2 n ≤ 1 / (n : ℝ) ^ 9 := by
  rw [stepSizeAdopted2]
  have h : ChainDrift.stepSize n 7 ≤ 1 / (n : ℝ) ^ (7 + 2) := ChainDrift.stepSize_le hn
  norm_num at h ⊢
  exact h

theorem stepSizeAdopted2_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ stepSizeAdopted2 n := by
  rw [stepSizeAdopted2, ChainDrift.stepSize, ChainDrift.horizon]
  have : (0 : ℝ) ≤ Real.log n := le_trans (by norm_num) (ChainDrift.log_pos_of_three hn)
  positivity

/-- **`η ≤ √2 · n⁻³`** — the per-step threshold `√(2 h d n)` at `h ≤ n⁻⁹`, `d ≤ n²`.
(`Discharge.eta_le` gives `√2 · n⁻²` at `h ≤ n⁻⁷`.) -/
theorem eta2_le {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt (2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ Real.sqrt 2 / (n : ℝ) ^ 3 := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hd := Discharge.card_UT_le_sq hn1
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hh := stepSizeAdopted2_le hn
  have hbound : 2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
      ≤ 2 / (n : ℝ) ^ 6 := by
    have hA : stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ≤ (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 :=
      mul_le_mul hh hd hd0 (by positivity)
    have h1 : 2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
        ≤ 2 * (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 * (n : ℝ) := by nlinarith [hA, hnR]
    calc 2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
        ≤ 2 * (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 * (n : ℝ) := h1
      _ = 2 / (n : ℝ) ^ 6 := by field_simp
  calc Real.sqrt (2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ Real.sqrt (2 / (n : ℝ) ^ 6) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt 2 / (n : ℝ) ^ 3 := by
        rw [Real.sqrt_div' 2 (by positivity), show ((n : ℝ) ^ 6) = ((n : ℝ) ^ 3) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]

/-- **The union-bound cost at the new `N`: `≤ 33 n⁹ log n`.**  (`Discharge.stepGood_cost_le` gives
`33 n⁷ log n` at `N = ⌈16 n⁵ log n⌉`.) -/
theorem stepGood_cost2_le {n : ℕ} (hn : 3 ≤ n) :
    ((numStepsAdopted2 n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2)
      ≤ 33 * (n : ℝ) ^ 9 * Real.log n := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog1 : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hN : ((numStepsAdopted2 n : ℕ) : ℝ) ≤ 16 * (n : ℝ) ^ 7 * Real.log n + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hd := Discharge.card_UT_le_sq hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
  have hstep : ((numStepsAdopted2 n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2)
      ≤ (16 * (n : ℝ) ^ 7 * Real.log n + 1) * ((n : ℝ) ^ 2 * 2) := by
    have h1 : (Fintype.card (UT n) : ℝ) * 2 ≤ (n : ℝ) ^ 2 * 2 := by linarith
    have hc0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) * 2 := by positivity
    have hb0 : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 7 * Real.log n + 1 := by nlinarith [hlog1, hpow]
    exact mul_le_mul hN h1 hc0 hb0
  refine le_trans hstep ?_
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h7 : (2 : ℝ) ≤ (n : ℝ) ^ 7 := by
    have h3 : (3 : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 := by gcongr
    norm_num at h3
    linarith
  have hslack : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 9 * Real.log n := by
    have ha : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 9 := by
      nlinarith [mul_nonneg hn2 (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ 7 - 2)]
    have hc : (n : ℝ) ^ 9 ≤ (n : ℝ) ^ 9 * Real.log n := by
      nlinarith [hlog1, pow_nonneg hn0.le 9]
    linarith
  nlinarith [hslack, hlog1, pow_nonneg hn0.le 9,
    mul_nonneg (pow_nonneg hn0.le 9) (by linarith : (0:ℝ) ≤ Real.log n)]

end

end D5.S3.Arith.Lattices.Klartag.Completion.ParamsAdopted2
