/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentRows10To17
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of normalized short-gap table rows 10 through 17. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData

/-! Checked rows 10 through 17 of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

-- The complete fixed-point model is evaluated by kernel reduction for each row.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Rows 10 through 17 in grid order. -/
def rows10To17 : List CheckedBox := [
  ⟨mkBox (15 / 4) 4 0 (1 / 4) (939 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox (29 / 8) (15 / 4) (7 / 8) 1 (1525 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox (29 / 8) (15 / 4) (3 / 4) (7 / 8) (345 / 64), by constructor <;> decide +kernel⟩,
  ⟨mkBox (7 / 2) (29 / 8) (7 / 8) 1 (705 / 128), by constructor <;> decide +kernel⟩,
  ⟨mkBox (7 / 2) (29 / 8) (3 / 4) (7 / 8) (1277 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox (7 / 2) (15 / 4) (1 / 2) (3 / 4) (1151 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox (7 / 2) (15 / 4) (1 / 4) (1 / 2) (963 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox (7 / 2) (15 / 4) 0 (1 / 4) (51 / 16), by constructor <;> decide +kernel⟩
]

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
