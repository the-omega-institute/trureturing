/- GID: D5/S3/Arith/Lattices/Klartag/Completion/FinalDischarge
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/FinalDischarge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR2W2
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3W2
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8
import Mathlib
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataR
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.Walk.ChainInputDom
import D5.S3.Arith.Lattices.Klartag.Completion.WindowR
import D5.S3.Arith.Lattices.Klartag.Contact.ThetaTight
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathLight
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6b
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

namespace D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped5
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftInputsStopped
open D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
open scoped ENNReal NNReal RealInnerProductSpace

section Data

variable {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p}

theorem hq_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ i ∈ windowOfR2 α p m g, ∀ j ∈ windowOfR2 α p m g,
      (0 : ℝ) ≤ ⟪qC α i, qC α j⟫ :=
  fun i hi _ _ => (lattice_fieldsR hα hn).1 _ i (windowOfR2_subset hi)

theorem hne_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ i ∈ windowOfR2 α p m g, qC α i ≠ 0 := by
  intro y hy
  have hr := (lattice_fieldsR hα hn).2.2.2.2.2.1 y (windowOfR2_subset hy)
  have hnorm : ‖qC α y‖ = (α * ‖toE (m + 1) y‖) ^ 2 := norm_qC α y
  intro hzero
  rw [hzero, norm_zero] at hnorm
  nlinarith [hr, hnorm]

theorem kSet_A0C_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    A0C (m + 1) ∈ Chain.kSet (qC α) (windowOfR2 α p m g) :=
  fun y hy => le_of_lt ((lattice_fieldsR hα hn).2.1 y (windowOfR2_subset hy))

end Data

section Light

variable {p m : ℕ} [NeZero p] {α : ℝ} {g : Fin (m + 1) → ZMod p}

end Light

section Path

variable {p m : ℕ} {α C' : ℝ} {g : Fin (m + 1) → ZMod p}

end Path

section Final

variable {c₃ : ℕ → ℝ} {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {C' : ℝ}

end Final

end D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge
