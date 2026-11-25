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

/-- Concatenate successive column slices, starting at the given column. -/
def shiftRowSlices (c : Certificate) (s k start : ℕ) :
    List ℕ → List (AffineRate × ℤ)
  | [] => []
  | count :: counts =>
      shiftRowSlice c s k start count ++ shiftRowSlices c s k (start + count) counts

theorem shiftRowSlices_eq_drop (c : Certificate) (s k start : ℕ) (counts : List ℕ)
    (h : c.columns.length ≤ start + counts.sum) :
    shiftRowSlices c s k start counts = (shiftRow c s k).drop start := by
  induction counts generalizing start with
  | nil =>
      have hlen : (shiftRow c s k).length = c.columns.length := by
        simp only [shiftRow, shiftRowWithColumns, columnWeights, affineColumns, List.length_map]
      rw [shiftRowSlices, List.drop_eq_nil_of_le (by simpa only [hlen, List.sum_nil,
        Nat.add_zero] using h)]
  | cons count counts ih =>
      have htail : c.columns.length ≤ (start + count) + counts.sum := by
        simpa only [List.sum_cons, Nat.add_assoc] using h
      rw [shiftRowSlices, shiftRowSlice_eq, ih (start + count) htail, ← List.drop_drop,
        List.take_append_drop]

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
