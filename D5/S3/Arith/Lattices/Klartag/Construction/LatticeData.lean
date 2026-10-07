/- GID: D5/S3/Arith/Lattices/Klartag/Construction/LatticeData
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Construction/LatticeData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construction A lattices, covolumes and ellipsoid transfer. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.RawDataInst2

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Construction.LatticeData

open MeasureTheory
open Finset
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2

noncomputable section

section Restrict

variable {n p : ℕ} {α R : ℝ} {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)}
  {W W' : Finset (Fin n → ℤ)} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`NormData` restricts.** -/
theorem normData_mono (h : NormData n α q W A₀) (hsub : W' ⊆ W) : NormData n α q W' A₀ :=
  ⟨fun y hy => h.hnorm y (hsub hy), fun y hy => h.hinner y (hsub hy)⟩

end Restrict

section Coverage

variable {n : ℕ} {α : ℝ}

end Coverage

section Exists

end Exists

end

end D5.S3.Arith.Lattices.Klartag.Construction.LatticeData
