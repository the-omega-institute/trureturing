/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailHypsWindow
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailHypsWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3W2
import D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge

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

namespace D5.S3.Arith.Lattices.Klartag.Tail.TailHypsWindow

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupRW2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
open scoped ENNReal NNReal RealInnerProductSpace

variable {p m : ℕ} {α R : ℝ} {g : Fin (m + 1) → ZMod p}

theorem hq_j_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ j : (Fin (m + 1) → ℤ), ∀ i ∈ windowOfR2 α p m g, (0 : ℝ) ≤ ⟪qC α i, qC α j⟫ :=
  fun j i hi => (lattice_fieldsR hα hn).1 j i (windowOfR2_subset hi)

theorem hA₀_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ y ∈ windowOfR2 α p m g, (1 : ℝ) < ⟪A0C (m + 1), qC α y⟫ :=
  fun y hy => (lattice_fieldsR hα hn).2.1 y (windowOfR2_subset hy)

theorem hwin_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ y ∈ windowOfR2 α p m g,
      ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) :=
  fun y hy => (lattice_fieldsR hα hn).2.2.2.2.1 y (windowOfR2_subset hy)

theorem hr_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ y ∈ windowOfR2 α p m g, 0 < α * ‖toE (m + 1) y‖ :=
  fun y hy => (lattice_fieldsR hα hn).2.2.2.2.2.1 y (windowOfR2_subset hy)

theorem hy_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ k, k < ParamsAdopted2.numStepsAdopted2 (m + 1) → k ≠ 0 →
      ∀ y ∈ windowOfR2 α p m g,
        0 < yOf (a0C (m + 1)) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1))
          (α * ‖toE (m + 1) y‖) :=
  fun k hk hk0 y hy =>
    (lattice_fieldsR hα hn).2.2.2.2.2.2 k hk hk0 y (windowOfR2_subset hy)

/-- **The constraint process's tail at the window**, named in the argument order
`both_sums_windowR2` reads.  This is `TailSideSetup3W2.tailSideHyp_latZR'` at `W := shellR`, since
`windowOfR2 α p m g = (shellR α (m+1)).filter (· ∈ latZ p (m+1) g)` definitionally. -/
theorem hprop_win
    (hraw : RawDataR p (m + 1) α R (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
    (hn : 3 ≤ m + 1) :
    ∀ k, k < ParamsAdopted2.numStepsAdopted2 (m + 1) → k ≠ 0 →
      ∀ y ∈ windowOfR2 α p m g,
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))
            {ω | ∃ i ≤ k, constraintM (qC α) (windowOfR2 α p m g) (A0C (m + 1))
              (ChainSetup.step (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1)))) y i ω ≤ 0}
          ≤ ENNReal.ofReal (4 * Phi (yOf (a0C (m + 1))
              ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1))
              (α * ‖toE (m + 1) y‖))) :=
  TailSideSetup3W2.tailSideHyp_latZR' hraw hnd hn g

end D5.S3.Arith.Lattices.Klartag.Tail.TailHypsWindow
