/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffinePackedRowSlices
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compute packed affine row weights for a selected block of columns. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open private affineColumns columnWeights shiftRowWithColumns shiftRow
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep

/-- Slice the raw columns before packing and weighting them. -/
def shiftRowSlice (c : Certificate) (s k start count : ℕ) : List (AffineRate × ℤ) :=
  shiftRow { c with columns := (c.columns.drop start).take count } s k

theorem shiftRowSlice_eq (c : Certificate) (s k start count : ℕ) :
    shiftRowSlice c s k start count = ((shiftRow c s k).drop start).take count := by
  simp only [shiftRowSlice, shiftRow, shiftRowWithColumns, affineColumns, columnWeights,
    List.map_drop, List.map_take]

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
