/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6c
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6c
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6b
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

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6c

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open scoped NNReal RealInnerProductSpace

/-- **The uniform contact threshold**, `n^{11/4} = n²·(√√n)³`. -/
noncomputable def c3Adopted'' (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.sqrt (Real.sqrt (n : ℝ)) ^ 3

theorem c3_adopted_nonnegative (n : ℕ) : 0 ≤ c3Adopted'' n := by
  rw [c3Adopted'']; positivity

theorem c3Adopted''_pos {n : ℕ} (hn : 0 < n) : 0 < c3Adopted'' n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hn0)
  rw [c3Adopted'']
  exact mul_pos (pow_pos hn0 2) (pow_pos hq 3)

/-- `n² = q^8` for `q = √√n`. -/
theorem sq_eq_qrt {n : ℕ} (hn : 0 ≤ (n : ℝ)) :
    (n : ℝ) ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) ^ 8 := by
  have h4 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn
  have hrw : (Real.sqrt (Real.sqrt (n : ℝ)) ^ 4) ^ 2
      = Real.sqrt (Real.sqrt (n : ℝ)) ^ 8 := by ring
  rw [← hrw, h4]

/-- `n³ = q^12` for `q = √√n`. -/
theorem cube_eq_qrt {n : ℕ} (hn : 0 ≤ (n : ℝ)) :
    (n : ℝ) ^ 3 = Real.sqrt (Real.sqrt (n : ℝ)) ^ 12 := by
  have h4 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn
  have hrw : (Real.sqrt (Real.sqrt (n : ℝ)) ^ 4) ^ 3
      = Real.sqrt (Real.sqrt (n : ℝ)) ^ 12 := by ring
  rw [← hrw, h4]

/-- **`x ≤ 2/√√n`.**  `c₃''·η ≤ q^11·√2/q^12 = √2/q`.  So `x → 0` like `n^{−1/4}`. -/
theorem c3eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    c3Adopted'' n * DriftStopped6.etaAdopted n ≤ 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hq : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hqne : Real.sqrt (Real.sqrt (n : ℝ)) ≠ 0 := ne_of_gt hq0
  have hηnn : 0 ≤ DriftStopped6.etaAdopted n := DriftStopped7.etaAdopted_nonneg (n := n)
  have hη : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 :=
    ParamsAdopted2.eta2_le (by omega)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hc0 : 0 ≤ c3Adopted'' n := c3_adopted_nonnegative n
  have hinv : (0 : ℝ) ≤ 1 / Real.sqrt (Real.sqrt (n : ℝ)) := by positivity
  have hval : c3Adopted'' n * (Real.sqrt 2 / (n : ℝ) ^ 3)
      = Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [c3Adopted'', sq_eq_qrt hn0.le, cube_eq_qrt hn0.le]
    field_simp
  calc c3Adopted'' n * DriftStopped6.etaAdopted n
      ≤ c3Adopted'' n * (Real.sqrt 2 / (n : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hη hc0
    _ = Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)) := hval
    _ = Real.sqrt 2 * (1 / Real.sqrt (Real.sqrt (n : ℝ))) := div_eq_mul_one_div _ _
    _ ≤ 2 * (1 / Real.sqrt (Real.sqrt (n : ℝ))) := mul_le_mul_of_nonneg_right hs2 hinv
    _ = 2 / Real.sqrt (Real.sqrt (n : ℝ)) := (div_eq_mul_one_div _ _).symm

/-- `x ≤ 1/4`, the hypothesis every `GoodPathBounds` statement takes. -/
theorem c3Adopted''_eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    c3Adopted'' n * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  have h := c3eta_le hn
  have hq : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have h2 : 2 / Real.sqrt (Real.sqrt (n : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq0 (by norm_num)]
    linarith
  linarith

section Count
variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

end Count

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6c
