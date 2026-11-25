/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/GroupedRows1
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

private theorem row_16 : quartic.checkRow 16 = true := by
  decide +kernel

private theorem row_17 : quartic.checkRow 17 = true := by
  decide +kernel

private theorem row_18 : quartic.checkRow 18 = true := by
  decide +kernel

private theorem row_19 : quartic.checkRow 19 = true := by
  decide +kernel

private theorem row_20 : quartic.checkRow 20 = true := by
  decide +kernel

private theorem row_21 : quartic.checkRow 21 = true := by
  decide +kernel

private theorem row_22 : quartic.checkRow 22 = true := by
  decide +kernel

private theorem row_23 : quartic.checkRow 23 = true := by
  decide +kernel

private theorem row_24 : quartic.checkRow 24 = true := by
  decide +kernel

private theorem row_25 : quartic.checkRow 25 = true := by
  decide +kernel

private theorem row_26 : quartic.checkRow 26 = true := by
  decide +kernel

private theorem row_27 : quartic.checkRow 27 = true := by
  decide +kernel

private theorem row_28 : quartic.checkRow 28 = true := by
  decide +kernel

private theorem row_29 : quartic.checkRow 29 = true := by
  decide +kernel

private theorem row_30 : quartic.checkRow 30 = true := by
  decide +kernel

private theorem row_31 : quartic.checkRow 31 = true := by
  decide +kernel

theorem rows_1 : (List.range' 16 16).all quartic.checkRow = true := by
  have h : List.range' 16 16 = [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := by decide +kernel
  rw [h]
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    row_16, row_17, row_18, row_19, row_20, row_21,
    row_22, row_23, row_24, row_25, row_26, row_27,
    row_28, row_29, row_30, row_31]

end

end RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks
