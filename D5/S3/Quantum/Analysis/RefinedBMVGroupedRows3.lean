/- GID: D5/S3/Quantum/Analysis/RefinedBMVGroupedRows3
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A block of kernel-checked signs for the refined BMV scalar certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMVGroupedData

/-! Kernel-checked signs for a block of X-prefixes. -/

namespace RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks

section

set_option maxRecDepth 40000
-- Each row checks the complete list of Y-prefixes.
set_option maxHeartbeats 0

private theorem row_48 : quartic.checkRow 48 = true := by
  decide +kernel

private theorem row_49 : quartic.checkRow 49 = true := by
  decide +kernel

private theorem row_50 : quartic.checkRow 50 = true := by
  decide +kernel

private theorem row_51 : quartic.checkRow 51 = true := by
  decide +kernel

private theorem row_52 : quartic.checkRow 52 = true := by
  decide +kernel

private theorem row_53 : quartic.checkRow 53 = true := by
  decide +kernel

private theorem row_54 : quartic.checkRow 54 = true := by
  decide +kernel

private theorem row_55 : quartic.checkRow 55 = true := by
  decide +kernel

private theorem row_56 : quartic.checkRow 56 = true := by
  decide +kernel

private theorem row_57 : quartic.checkRow 57 = true := by
  decide +kernel

private theorem row_58 : quartic.checkRow 58 = true := by
  decide +kernel

private theorem row_59 : quartic.checkRow 59 = true := by
  decide +kernel

private theorem row_60 : quartic.checkRow 60 = true := by
  decide +kernel

private theorem row_61 : quartic.checkRow 61 = true := by
  decide +kernel

private theorem row_62 : quartic.checkRow 62 = true := by
  decide +kernel

private theorem row_63 : quartic.checkRow 63 = true := by
  decide +kernel

private theorem row_64 : quartic.checkRow 64 = true := by
  decide +kernel

theorem rows_3 : (List.range' 48 17).all quartic.checkRow = true := by
  have h : List.range' 48 17 = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64] := by decide +kernel
  rw [h]
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    row_48, row_49, row_50, row_51, row_52, row_53,
    row_54, row_55, row_56, row_57, row_58, row_59,
    row_60, row_61, row_62, row_63, row_64]

end

end RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks
