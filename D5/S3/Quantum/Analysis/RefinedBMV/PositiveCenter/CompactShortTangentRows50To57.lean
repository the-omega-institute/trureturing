/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentRows50To57
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of normalized short-gap table rows 50 through 57. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData

/-! Checked rows 50 through 57 of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

-- The complete fixed-point model is evaluated by kernel reduction for each row.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Rows 50 through 57 in grid order. -/
def rows50To57 : List CheckedBox := [
  ⟨mkBox (7 / 4) 2 (1 / 2) (3 / 4) (477 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (7 / 4) 2 (1 / 4) (1 / 2) (421 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (7 / 4) 2 0 (1 / 4) (377 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (3 / 2) (7 / 4) (3 / 4) 1 (31 / 16) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (3 / 2) (7 / 4) (1 / 2) (3 / 4) (435 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (3 / 2) (7 / 4) (1 / 4) (1 / 2) (387 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (3 / 2) (7 / 4) 0 (1 / 4) (175 / 128) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (5 / 4) (3 / 2) (3 / 4) 1 (113 / 64) 19 22 6, by constructor <;> decide +kernel⟩
]

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
