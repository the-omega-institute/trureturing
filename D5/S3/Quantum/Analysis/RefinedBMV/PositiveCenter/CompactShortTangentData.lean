/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentData
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common Taylor orders and score threshold for the short-gap replay. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortBox

/-! Box data and the certificate type used by the short-gap replay. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

/-- Form a box with the common truncation orders for the normalized short-gap table. -/
def mkBox (uLo uHi dLo dHi root : ℚ) : CompactShortBox :=
  ⟨uLo, uHi, dLo, dHi, root, 29, 32, 6⟩

/-- All box checks, with one fixed-point unit as the positive score endpoint.
The lower checker tries the direct estimate first and uses degree zero for its fallback. -/
abbrev CheckedBox := {box : CompactShortBox // box.Checks 0 1}

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
