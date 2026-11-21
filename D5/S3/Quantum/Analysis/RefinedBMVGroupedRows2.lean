/- GID: D5/S3/Quantum/Analysis/RefinedBMVGroupedRows2
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

private theorem row_32 : quartic.checkRow 32 = true := by
  decide +kernel

private theorem row_33 : quartic.checkRow 33 = true := by
  decide +kernel

private theorem row_34 : quartic.checkRow 34 = true := by
  decide +kernel

private theorem row_35 : quartic.checkRow 35 = true := by
  decide +kernel

private theorem row_36 : quartic.checkRow 36 = true := by
  decide +kernel

private theorem row_37 : quartic.checkRow 37 = true := by
  decide +kernel

private theorem row_38 : quartic.checkRow 38 = true := by
  decide +kernel

private theorem row_39 : quartic.checkRow 39 = true := by
  decide +kernel

private theorem row_40 : quartic.checkRow 40 = true := by
  decide +kernel

private theorem row_41 : quartic.checkRow 41 = true := by
  decide +kernel

private theorem row_42 : quartic.checkRow 42 = true := by
  decide +kernel

private theorem row_43 : quartic.checkRow 43 = true := by
  decide +kernel

private theorem row_44 : quartic.checkRow 44 = true := by
  decide +kernel

private theorem row_45 : quartic.checkRow 45 = true := by
  decide +kernel

private theorem row_46 : quartic.checkRow 46 = true := by
  decide +kernel

private theorem row_47 : quartic.checkRow 47 = true := by
  decide +kernel

theorem rows_2 : (List.range' 32 16).all quartic.checkRow = true := by
  have h : List.range' 32 16 = [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] := by decide +kernel
  rw [h]
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    row_32, row_33, row_34, row_35, row_36, row_37,
    row_38, row_39, row_40, row_41, row_42, row_43,
    row_44, row_45, row_46, row_47]

end

end RefinedBMV.DividedDifference.SparseExpansion.GroupedMasks
