/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentRows26To33
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of normalized short-gap table rows 26 through 33. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData

/-! Checked rows 26 through 33 of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

-- The complete fixed-point model is evaluated by kernel reduction for each row.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Rows 26 through 33 in grid order. -/
def rows26To33 : List CheckedBox := [
  ⟨mkBox (25 / 8) (13 / 4) (3 / 4) (7 / 8) (511 / 128) 21 24 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox 3 (25 / 8) (3 / 4) 1 (997 / 256) 25 28 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox 3 (13 / 4) (1 / 2) (3 / 4) (863 / 256) 21 24 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox 3 (13 / 4) (1 / 4) (1 / 2) (183 / 64) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox 3 (13 / 4) 0 (1 / 4) (629 / 256) 19 22 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (23 / 8) 3 (3 / 4) 1 (929 / 256) 23 26 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (11 / 4) (23 / 8) (3 / 4) 1 (867 / 256) 21 24 6, by constructor <;> decide +kernel⟩,
  ⟨mkBox (11 / 4) 3 (1 / 2) (3 / 4) (755 / 256) 19 22 6, by constructor <;> decide +kernel⟩
]

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
