/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentRows66To72
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of normalized short-gap table rows 66 through 72. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData

/-! Checked rows 66 through 72 of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

-- The complete fixed-point model is evaluated by kernel reduction for each row.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Rows 66 through 72 in grid order. -/
def rows66To72 : List CheckedBox := [
  ⟨mkBox (3 / 4) 1 (1 / 2) (3 / 4) (173 / 128) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (3 / 4) 1 (1 / 4) (1 / 2) (79 / 64) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (3 / 4) 1 0 (1 / 4) (293 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (1 / 2) (3 / 4) (3 / 4) 1 (359 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (1 / 2) (3 / 4) (1 / 2) (3 / 4) (163 / 128) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (1 / 2) (3 / 4) (1 / 4) (1 / 2) (75 / 64) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (1 / 2) (3 / 4) 0 (1 / 4) (281 / 256) 19 22 6, by constructor <;> decide +kernel⟩
]

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
