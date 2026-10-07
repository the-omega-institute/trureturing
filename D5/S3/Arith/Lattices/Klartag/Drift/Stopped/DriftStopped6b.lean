/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6b
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6b
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped7

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6b

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open scoped NNReal RealInnerProductSpace

theorem cqAt_le_half {n : ℕ} {c₃ : ℝ} (hn : 2073600 ≤ n) (hc₃0 : 0 ≤ c₃)
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    GoodPathBounds.cqAt n c₃ ≤ 1 / 2 := by
  have h := GoodPathBounds.two_le_cqAt_den hn hc₃ hc₃0
  rw [GoodPathBounds.cqAt]
  exact one_div_le_one_div_of_le (by norm_num) h

/-- **`C₁ ≤ 3√n`** at any admissible `c₃` — `DriftStopped7.C₁_le` with `mAdopted`/`cAdopted`
replaced by `mAt`/`cqAt`. -/
theorem C₁_le_at {n : ℕ} {c₃ : ℝ} (hn : 2073600 ≤ n) (hc₃0 : 0 ≤ c₃)
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
      ≤ 3 * Real.sqrt (n : ℝ) := by
  have hm := GoodPathBounds.half_le_mAt hn hc₃
  have hc := cqAt_le_half hn hc₃0 hc₃
  have hs := DriftStopped7.sqrt_ge_1440 hn
  have hdiv : Real.sqrt (n : ℝ) / GoodPathBounds.mAt n c₃ ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.sqrt_nonneg ((n : ℝ)), hm, hs]
  rw [DriftStopped4.C₁]
  linarith

/-- **`SlackHyp` at any admissible `c₃`** — `DriftStopped7.slackHyp_adopted` re-proved at `mAt`,
`cqAt`.  `C₁·2B ≤ 3√n·10/n³ = 30/(n²√n) ≤ 1 = slackAdopted`. -/
theorem slackHyp_at {n : ℕ} {c₃ : ℝ} (hn : 2073600 ≤ n) (hc₃0 : 0 ≤ c₃)
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    DriftStopped4.SlackHyp n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
      (B_adopted n) DriftStopped6.slackAdopted := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hC := C₁_le_at hn hc₃0 hc₃
  have hB := DriftStopped7.B_adopted_le' hn
  have hB0 := DriftStopped7.B_adopted_nonneg hn
  have hC0 : 0 ≤ DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃) :=
    DriftStopped4.C₁_nonneg (GoodPathBounds.cqAt_nonneg hn hc₃ hc₃0)
      (by have := GoodPathBounds.half_le_mAt hn hc₃; linarith)
  have hstep : DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
        * (2 * B_adopted n)
      ≤ (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3)) :=
    mul_le_mul hC (by linarith) (by linarith) (by positivity)
  have hfin : (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3)) ≤ 1 := by
    have hn2 : (30 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hnR, hn0]
    have hcube : 30 * (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith [hn2, hn0]
    have hsq : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg ((n : ℝ)),
        DriftStopped7.sqrt_ge_1440 hn]
    have hval : (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3))
        = 30 * Real.sqrt (n : ℝ) / (n : ℝ) ^ 3 := by ring
    rw [hval, div_le_one (by positivity)]
    linarith
  rw [DriftStopped4.SlackHyp, DriftStopped6.slackAdopted]
  linarith

section Count
variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

end Count

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6b
