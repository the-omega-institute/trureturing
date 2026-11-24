/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentRows58To65
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of normalized short-gap table rows 58 through 65. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData

/-! Checked rows 58 through 65 of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

-- The complete fixed-point model is evaluated by kernel reduction for each row.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Rows 58 through 65 in grid order. -/
def rows58To65 : List CheckedBox := [
  ⟨mkBox (5 / 4) (3 / 2) (1 / 2) (3 / 4) (399 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox (5 / 4) (3 / 2) (1 / 4) (1 / 2) (179 / 128), by constructor <;> decide +kernel⟩,
  ⟨mkBox (5 / 4) (3 / 2) 0 (1 / 4) (327 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox 1 (5 / 4) (3 / 4) 1 (415 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox 1 (5 / 4) (1 / 2) (3 / 4) (185 / 128), by constructor <;> decide +kernel⟩,
  ⟨mkBox 1 (5 / 4) (1 / 4) (1 / 2) (335 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox 1 (5 / 4) 0 (1 / 4) (77 / 64), by constructor <;> decide +kernel⟩,
  ⟨mkBox (3 / 4) 1 (3 / 4) 1 (385 / 256), by constructor <;> decide +kernel⟩
]

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
