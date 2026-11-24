/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentRows42To49
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of normalized short-gap table rows 42 through 49. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData

/-! Checked rows 42 through 49 of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

-- The complete fixed-point model is evaluated by kernel reduction for each row.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Rows 42 through 49 in grid order. -/
def rows42To49 : List CheckedBox := [
  ⟨mkBox (9 / 4) (5 / 2) (1 / 2) (3 / 4) (591 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox (9 / 4) (5 / 2) (1 / 4) (1 / 2) 2, by constructor <;> decide +kernel⟩,
  ⟨mkBox (9 / 4) (5 / 2) 0 (1 / 4) (451 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox 2 (9 / 4) (3 / 4) 1 (307 / 128), by constructor <;> decide +kernel⟩,
  ⟨mkBox 2 (9 / 4) (1 / 2) (3 / 4) (529 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox 2 (9 / 4) (1 / 4) (1 / 2) (463 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox 2 (9 / 4) 0 (1 / 4) (411 / 256), by constructor <;> decide +kernel⟩,
  ⟨mkBox (7 / 4) 2 (3 / 4) 1 (275 / 128), by constructor <;> decide +kernel⟩
]

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
