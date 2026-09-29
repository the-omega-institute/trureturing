/- GID: D5/S3/Quantum/Entanglement/SectorSchmidtEncoding
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorSchmidtEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sector-dependent flat target factors and residual spectra define actual isometric encodings. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.SectorSchmidtEncoding

open scoped BigOperators

variable {Sector Coord : Type*} [Fintype Sector] [DecidableEq Sector]
  [Fintype Coord] [DecidableEq Coord]

/-- One physical side of the source encoding in (36.1). -/
abbrev SourceLocal (d : Sector → ℕ) :=
  Sigma (fun s : Sector => Fin (d s) × Coord)

/-- One physical side of the flat target encoding in (36.1). -/
abbrev TargetLocal (d : Sector → ℕ) :=
  Sigma (fun s : Sector => Fin (d s))

/-- Source isometry, with each residual Schmidt coefficient repeated `d s` times. -/
def sourceEncoding (d : Sector → ℕ) (spectrum : Sector → Coord → ℝ) :
    Matrix (SourceLocal (Coord := Coord) d × SourceLocal (Coord := Coord) d) Sector ℂ :=
  fun xy s =>
    if xy.1 = xy.2 ∧ xy.1.1 = s then
      (Real.sqrt (spectrum xy.1.1 xy.1.2.2 / (d xy.1.1 : ℝ)) : ℂ)
    else 0

/-- Flat target isometry, retaining the same sector-dependent target rank. -/
def targetEncoding (d : Sector → ℕ) :
    Matrix (TargetLocal d × TargetLocal d) Sector ℂ :=
  fun xy s =>
    if xy.1 = xy.2 ∧ xy.1.1 = s then
      (Real.sqrt ((d xy.1.1 : ℝ)⁻¹) : ℂ)
    else 0


end D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
