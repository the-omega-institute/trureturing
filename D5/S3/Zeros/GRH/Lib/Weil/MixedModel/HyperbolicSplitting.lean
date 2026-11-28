/- GID: D5/S3/Zeros/GRH/Lib/Weil/MixedModel/HyperbolicSplitting
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/MixedModel/HyperbolicSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.MixedModel.HyperbolicSplitting. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/MixedModel/HyperbolicSplitting.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.ZeroTermLaw
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Standard polarisation of the hyperbolic space as a splitting. -/

/-- The splitting of hyperbolic space of rank 2p over the zero space, with l the first p and k
the last p basis vectors. -/
noncomputable def hyperbolicSplitting E p [Field E] [CMType E] [WeilData E] [Fintype p] :
  (hypSpace E p).Splitting (stdSpace E Empty)
  p := by use .fromRows 0 1, .fromRows 1 0, 0 <;> first | (ext ⟨⟩; done) | simp +arith
