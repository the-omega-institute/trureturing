/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentRows02To09
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of normalized short-gap table rows 2 through 9. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData

/-! Checked rows 2 through 9 of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

-- The complete fixed-point model is evaluated by kernel reduction for each row.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Rows 2 through 9 in grid order. -/
def rows02To09 : List CheckedBox := [
  ⟨mkBox (31 / 8) (63 / 16) (7 / 8) 1 (1755 / 256) 27 30 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (31 / 8) 4 (3 / 4) (7 / 8) (1617 / 256) 25 28 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (61 / 16) (31 / 8) (7 / 8) 1 (1685 / 256) 27 30 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (15 / 4) (61 / 16) (7 / 8) 1 (1619 / 256) 27 30 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (15 / 4) (31 / 8) (3 / 4) (7 / 8) (1493 / 256) 25 28 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (31 / 8) 4 (1 / 2) (3 / 4) (1395 / 256) 25 28 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (15 / 4) (31 / 8) (1 / 2) (3 / 4) (645 / 128) 25 28 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (15 / 4) 4 (1 / 4) (1 / 2) (1115 / 256) 23 26 6, by constructor <;> decide +kernel⟩
]

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
