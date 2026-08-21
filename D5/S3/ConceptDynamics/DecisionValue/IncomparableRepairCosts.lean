/- GID: D5/S3/ConceptDynamics/DecisionValue/IncomparableRepairCosts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/IncomparableRepairCosts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite two-repair cost face has two distinct Pareto-minimal incomparable receipts. -/

import D5.S3.ResourceOrder.PriceFaceOrder

/- Library-search audit trail (2026-08-21):
   * Exact repository hit `PriceFaceOrder.trade_face_two_incomparable_minima`
     already proves the finite two-receipt Pareto-incomparability statement.
     This theorem is a direct addressable wrapper and intentionally does not
     redeclare the cost coordinates or re-prove their order facts.
   * The imported module records the pinned Mathlib support used by that exact
     result (`Filter.EventuallyLE` and `Minimal`).
   * `lake env loogle` and `lake env leansearch` are unavailable in this
     environment; no conclusion relies on those executables.
-/

namespace D5.S3.ConceptDynamics.DecisionValue.IncomparableRepairCosts

open D5.S3.Resource
open D5.S3.ResourceOrder.PriceFaceOrder

/-- In a finite two-repair cost face, the two repairs are distinct minimal
receipts and neither receipt is componentwise below the other. Consequently,
the formal cost structure alone does not select a unique repair. -/
theorem incomparable_repairs_no_unique_choice :
    tradeReceipt true ∈ tradeFace ∧
      tradeReceipt false ∈ tradeFace ∧
      tradeReceipt true ≠ tradeReceipt false ∧
      ¬ tradeReceipt true ≤ tradeReceipt false ∧
      ¬ tradeReceipt false ≤ tradeReceipt true := by
  exact trade_face_two_incomparable_minima

#print axioms incomparable_repairs_no_unique_choice

end D5.S3.ConceptDynamics.DecisionValue.IncomparableRepairCosts
