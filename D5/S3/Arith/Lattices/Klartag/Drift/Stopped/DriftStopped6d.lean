/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6d
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6d
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge2
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6c

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6d

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open scoped NNReal RealInnerProductSpace

theorem c3_eq {n : ℕ} (hn : 0 < n) :
    DriftStopped6c.c3Adopted'' n = FinalDischarge2.c3Adopted'' n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) :=
    Real.sqrt_pos.2 (Real.sqrt_pos.2 hn0)
  have hqne : Real.sqrt (Real.sqrt (n : ℝ)) ≠ 0 := ne_of_gt hq0
  rw [DriftStopped6c.c3Adopted'', FinalDischarge2.c3Adopted'',
    DriftStopped6c.sq_eq_qrt hn0.le, DriftStopped6c.cube_eq_qrt hn0.le, eq_div_iff hqne]
  ring

/-- **`x := c₃''·η ≤ 2/√√n`** — the slack term is decreasing, like `n^{−1/4}`. -/
theorem c3eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n
      ≤ 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  rw [← c3_eq (by omega)]; exact DriftStopped6c.c3eta_le hn

section Count
variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

end Count

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6d
