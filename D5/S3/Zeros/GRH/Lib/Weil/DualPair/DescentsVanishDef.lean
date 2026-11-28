/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/DescentsVanishDef
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/DescentsVanishDef
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.DescentsVanishDef. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/DescentsVanishDef.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.Lift
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairReal
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! A step of the proof of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth,
rapid decay.

This file: Predicate: all theta descents with data vacuum at given places vanish. -/

/-- All descents g ↦ ∫θ(ω_{a,1}(g,h)f)Y(h)dh of Y from U(V) to U(W) vanish, for data f that are
the vacuum at the places of S ∪ S̄. -/
def DescentsVanish {E n m} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] {s t} (W :
  Space E n s) (V : Space E m t) a S Y := ∀ f, Space.projOn _ S f = f →
  Space.lift (pairThetaKer W V a 1).swap f Y = 0
