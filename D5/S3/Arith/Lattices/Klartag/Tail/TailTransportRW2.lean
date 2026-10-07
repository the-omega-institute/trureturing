/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailTransportRW2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailTransportRW2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailTransport
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepRW2

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

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open ProbabilityTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
open scoped ENNReal NNReal

theorem tail_at_step_mu_rw2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (C : ℕ → Ω → Finset (Fin n → ℤ))
    (W : Finset (Fin n → ℤ)) (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))
    (hhit : ∀ k, k < N → ∀ y ∈ W,
      {ω | y ∈ C k ω} ⊆ {ω | ∃ j ≤ k, M y j ω ≤ 0})
    (hprop : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      μ {ω | ∃ j ≤ k, M y j ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))))
    (hzero : ∀ y ∈ W, μ.real {ω | y ∈ C 0 ω} = 0) :
    ∀ k, k < N → ∀ y ∈ W,
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStepRW2 α n hstep y k := by
  refine tail_at_stepRW2 C W hwin hr hy ?_ hzero
  intro k hk hk0 y hy'
  exact le_trans (measure_mono (hhit k hk y hy')) (hprop k hk hk0 y hy')

end D5.S3.Arith.Lattices.Klartag
