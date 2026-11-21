/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/GroupedRows0
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A block of kernel-checked signs for the refined BMV scalar certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedData

/-! Kernel-checked signs for a block of X-prefixes. -/

namespace RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks

section

set_option maxRecDepth 40000
-- Each row checks the complete list of Y-prefixes.
set_option maxHeartbeats 0

private theorem row_0 : quartic.checkRow 0 = true := by
  decide +kernel

private theorem row_1 : quartic.checkRow 1 = true := by
  decide +kernel

private theorem row_2 : quartic.checkRow 2 = true := by
  decide +kernel

private theorem row_3 : quartic.checkRow 3 = true := by
  decide +kernel

private theorem row_4 : quartic.checkRow 4 = true := by
  decide +kernel

private theorem row_5 : quartic.checkRow 5 = true := by
  decide +kernel

private theorem row_6 : quartic.checkRow 6 = true := by
  decide +kernel

private theorem row_7 : quartic.checkRow 7 = true := by
  decide +kernel

private theorem row_8 : quartic.checkRow 8 = true := by
  decide +kernel

private theorem row_9 : quartic.checkRow 9 = true := by
  decide +kernel

private theorem row_10 : quartic.checkRow 10 = true := by
  decide +kernel

private theorem row_11 : quartic.checkRow 11 = true := by
  decide +kernel

private theorem row_12 : quartic.checkRow 12 = true := by
  decide +kernel

private theorem row_13 : quartic.checkRow 13 = true := by
  decide +kernel

private theorem row_14 : quartic.checkRow 14 = true := by
  decide +kernel

private theorem row_15 : quartic.checkRow 15 = true := by
  decide +kernel

theorem rows_0 : (List.range' 0 16).all quartic.checkRow = true := by
  have h : List.range' 0 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide +kernel
  rw [h]
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    row_0, row_1, row_2, row_3, row_4, row_5,
    row_6, row_7, row_8, row_9, row_10, row_11,
    row_12, row_13, row_14, row_15]

end

end RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks
