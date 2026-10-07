/- GID: D5/S3/Arith/Lattices/Klartag/Completion/FailTotalBound99
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/FailTotalBound99
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.ExpDecay99
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.FailTotalBound99

open D5.S3.Arith.Lattices.Klartag

variable {n : ℕ}

/-- `N ≤ 16·n⁷·log n + 1` — `numStepsAdopted2` is a `Nat.ceil`. -/
theorem numSteps_le (hn : 1 ≤ n) :
    ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) ≤ 16 * (n : ℝ) ^ 7 * Real.log n + 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [ParamsAdopted2.numStepsAdopted2, ChainDrift.numSteps]
  exact le_of_lt (Nat.ceil_lt_add_one (by positivity))

/-- **The polynomial factor of the two exponential terms is at most `173·n¹⁰`.** -/
theorem poly_le (hn : 1 ≤ n) :
    (33 * (n : ℝ) ^ 9 * Real.log n + 4)
        + 8 * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
      ≤ 173 * (n : ℝ) ^ 10 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : Real.log n ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hn0
    linarith
  have hN := numSteps_le hn
  have h1 : 33 * (n : ℝ) ^ 9 * Real.log n ≤ 33 * (n : ℝ) ^ 10 := by
    have h := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 33 * (n : ℝ) ^ 9 by positivity)
    linarith
  have h2 : 16 * (n : ℝ) ^ 7 * Real.log n ≤ 16 * (n : ℝ) ^ 8 := by
    have h := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 16 * (n : ℝ) ^ 7 by positivity)
    linarith
  have h3 : (n : ℝ) ^ 8 ≤ (n : ℝ) ^ 10 := by
    exact pow_le_pow_right₀ hnR (by norm_num)
  have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 10 := one_le_pow₀ hnR
  linarith

end D5.S3.Arith.Lattices.Klartag.Completion.FailTotalBound99
