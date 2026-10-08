/- GID: D5/S3/Arith/Lattices/Klartag/Completion/Threshold2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/Threshold2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.Threshold

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Threshold2

open MeasureTheory
open Metric
open Finset
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Completion.Threshold
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling

/-- **The threshold.**  `1440² = 2,073,600` — the cheaply provable `n₁` of
`HJ.junk_endpoint_le_three`, replacing `Threshold.n₁ = 839`. -/
def n₁ : ℕ := 2073600

/-- `Final.smallConst` at the new threshold. -/
noncomputable def smallConst : ℝ := Final.smallConst n₁

noncomputable def const (c₀ : ℝ) : ℝ := min c₀ smallConst

end D5.S3.Arith.Lattices.Klartag.Completion.Threshold2
