/- GID: D5/S3/Zeros/GRH/Lib/General/Groups/IndexOfProduct
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Groups/IndexOfProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Groups.IndexOfProduct. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Groups/IndexOfProduct.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.CM.Sigma.PadicSeriesDefs
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.CuspKernel.BesselSchurBound
import D5.S3.Zeros.GRH.Lib.Weil.Periods.DegreeOfT
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of group theory (textbook or folklore).

This file: Index of a finite product of subgroups is the product of indices. -/

lemma index_pi_univ {I G} [Fintype I] [∀ i, Group (G i)] H :
    (@Subgroup.pi I G _ .univ H).index = ∏ i, (H i).index :=
  (Nat.card_congr (QuotientGroup.leftRel_pi H ▸ Setoid.piQuotientEquiv _) ▸ Nat.card_pi :)
