/- GID: D5/S3/ResourceOrder/MarginalTradeAmplification
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/MarginalTradeAmplification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Marginal repricing amplifies marked value relative to traded cash. -/

import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-17):
   * Repository searches found no declaration for marginal repricing or the
     displayed marked-value-to-traded-cash ratio.
   * Pinned Mathlib has no market-specific statement, but supplies the exact
     algebraic core `abs_mul` and `abs_of_nonneg`; both are applied below.
-/

namespace D5.S3.ResourceOrder.MarginalTradeAmplification

/-- If marked value and traded cash are defined from the displayed price move
and the marginal trade, their ratio is the corresponding inventory-to-trade
amplification identity. -/
theorem marginal_trade_mark_amplification
    (shares priceBefore priceAfter tradeSize averagePrice markedChange tradeCash : Real)
    (hShares : 0 <= shares)
    (hMarked : markedChange = shares * (priceAfter - priceBefore))
    (hCash : tradeCash = tradeSize * averagePrice) :
    |markedChange| / tradeCash =
      shares * |priceAfter - priceBefore| / (tradeSize * averagePrice) := by
  rw [hMarked, hCash, abs_mul, abs_of_nonneg hShares]

#print axioms marginal_trade_mark_amplification

end D5.S3.ResourceOrder.MarginalTradeAmplification
