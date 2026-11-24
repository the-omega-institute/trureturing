/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentRows34To41
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of normalized short-gap table rows 34 through 41. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData

/-! Checked rows 34 through 41 of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

-- The complete fixed-point model is evaluated by kernel reduction for each row.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Rows 34 through 41 in grid order. -/
def rows34To41 : List CheckedBox := [
  ⟨mkBox (11 / 4) 3 (1 / 4) (1 / 2) (645 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (11 / 4) 3 0 (1 / 4) (559 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (21 / 8) (11 / 4) (3 / 4) 1 (811 / 256) 21 24 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (5 / 2) (21 / 8) (3 / 4) 1 (95 / 32) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (5 / 2) (11 / 4) (1 / 2) (3 / 4) (665 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (5 / 2) (11 / 4) (1 / 4) (1 / 2) (143 / 64) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (5 / 2) (11 / 4) 0 (1 / 4) (125 / 64) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (9 / 4) (5 / 2) (3 / 4) 1 (173 / 64) 21 24 6, by constructor <;> decide +kernel⟩
]

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
