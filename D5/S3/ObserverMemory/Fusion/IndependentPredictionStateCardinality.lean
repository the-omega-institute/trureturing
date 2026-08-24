/- GID: D5/S3/ObserverMemory/Fusion/IndependentPredictionStateCardinality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/IndependentPredictionStateCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two independent predictive components have a product quotient and multiplicative finite state count; general finite index families are not formalized. -/

import D5.S3.ObserverMemory.Fusion.IndependentProductCompletion

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'finite_independent_prediction_state_cardinality' D5
     Golden/Frozen/accepted` returned no matches.
   * Public repository hit `independent_product_completion` proves the substantive
     two-component predictive-quotient equivalence and is reused directly; no public
     declaration combines it with the exact finite cardinality formula.
   * Private hits in that module prove injectivity and surjectivity of the quotient map;
     they are implementation details and are not treated as cover declarations.
   * Pinned Mathlib exact hits `Nat.card_congr` and `Nat.card_prod` turn the imported
     equivalence into the state-count formula. `Quotient.finChoice`,
     `Quotient.finChoiceEquiv`, `Setoid.prod`, and `prodQuotientEquiv` exist upstream,
     but the imported repository theorem already supplies the needed decomposition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Fusion.IndependentPredictionStateCardinality

open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open D5.S3.ObserverMemory.Fusion.IndependentProductCompletion

/-- The number of predictive states, read as the finite cardinality of its carrier. -/
noncomputable def predictiveStateCount (State : Type*) : Nat :=
  Nat.card State

/-- For two independent component systems, modeled by componentwise update and readout,
the global predictive quotient decomposes as their product and its finite state count
is the product, rather than the sum, of the component state counts. -/
theorem finite_independent_prediction_state_cardinality
    {Y₁ Y₂ O₁ O₂ : Type*}
    (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂)
    [Finite (CompletedState tau₁ q₁)] [Finite (CompletedState tau₂ q₂)] :
    Nonempty
        (CompletedState (productUpdate tau₁ tau₂) (productReadout q₁ q₂) ≃
          CompletedState tau₁ q₁ × CompletedState tau₂ q₂) ∧
      predictiveStateCount
          (CompletedState (productUpdate tau₁ tau₂) (productReadout q₁ q₂)) =
        predictiveStateCount (CompletedState tau₁ q₁) *
          predictiveStateCount (CompletedState tau₂ q₂) := by
  obtain ⟨equivalence⟩ :=
    (independent_product_completion tau₁ tau₂ q₁ q₂).1
  refine ⟨⟨equivalence⟩, ?_⟩
  simpa only [predictiveStateCount, Nat.card_prod] using Nat.card_congr equivalence

example :
    predictiveStateCount
        (CompletedState (productUpdate (id : Unit → Unit) (id : Unit → Unit))
          (productReadout (id : Unit → Unit) (id : Unit → Unit))) =
      predictiveStateCount (CompletedState (id : Unit → Unit) id) *
        predictiveStateCount (CompletedState (id : Unit → Unit) id) :=
  (finite_independent_prediction_state_cardinality
    (id : Unit → Unit) (id : Unit → Unit)
    (id : Unit → Unit) (id : Unit → Unit)).2

#print axioms finite_independent_prediction_state_cardinality

end D5.S3.ObserverMemory.Fusion.IndependentPredictionStateCardinality
