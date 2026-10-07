/- GID: D5/S3/Arith/Lattices/Klartag/State/StateSupply
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/StateSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.ThetaTight
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8
import Mathlib
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataR
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftInputsStopped
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3

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

namespace D5.S3.Arith.Lattices.Klartag.State.StateSupply

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2R
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open scoped ENNReal RealInnerProductSpace

section Data

variable {p m : ℕ} {α R : ℝ} {g : Fin (m + 1) → ZMod p}

/-- `symMat A₀ = a₀ • 1`, from `A0C = a₀ • idUT` and `symMat_idUT`. -/
theorem symMat_A0C (n : ℕ) :
    symMat (A0C n) = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [A0C, StateInvariant.symMat_smul, symMat_idUT]

end Data

section Assembly

end Assembly

end D5.S3.Arith.Lattices.Klartag.State.StateSupply
