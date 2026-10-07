/- GID: D5/S3/Arith/Lattices/Klartag/Completion/FinalDischarge2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/FinalDischarge2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

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

namespace D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge2

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

noncomputable def c3Adopted'' (n : ℕ) : ℝ := (n : ℝ) ^ 3 / Real.sqrt (Real.sqrt (n : ℝ))

theorem c3_adopted_nonnegative (n : ℕ) : 0 ≤ c3Adopted'' n := by
  rw [c3Adopted'']; positivity

section HS

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {P : Measure Ω} [IsProbabilityMeasure P]

end HS

end D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge2
