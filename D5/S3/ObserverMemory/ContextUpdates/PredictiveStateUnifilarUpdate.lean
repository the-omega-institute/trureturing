/- GID: D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete future laws induce an almost-sure single-valued predictive-state update. -/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/- Library-search audit trail (2026-08-28):
   * Current-tree body-shape searches for full future laws, conditional PMFs,
     stream-law quotients, and predictive-state updates found no exact theorem
     on probability measures over infinite symbol streams. The closest frozen
     result, `predictive_equivalence_preserved_by_positive_conditioning`, is
     restricted to finite future records and is therefore not an exact hit.
   * Pinned Mathlib supplies the exact carrier `ProbabilityMeasure`, the
     canonical operations `Measure.restrict` and `Measure.map`, `Quotient.lift`,
     `ProbabilityMeasure.toMeasure_injective`, and `ae_iff_of_countable`; each
     is applied directly below. No pinned theorem packages the quotient update.
   * External Loogle and LeanSearch executables were unavailable. -/

namespace D5.S3.ObserverMemory.ContextUpdates.PredictiveStateUnifilarUpdate

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Histories are identified exactly when their probability measures on the
complete infinite future agree. If extension by a positive-probability symbol
realizes the canonical conditioned tail law, history extension descends to a
single-valued predictive-state update. The update computes on every positive
symbol and hence almost everywhere under the next-symbol marginal. -/
theorem unifilar_predictive_update
    {History Symbol : Type*} [MeasurableSpace Symbol]
    [MeasurableSingletonClass Symbol] [Countable Symbol]
    (futureLaw : History -> ProbabilityMeasure (Nat -> Symbol))
    (extendHistory : History -> Symbol -> History)
    (conditionedExtension : forall history symbol,
      0 < (futureLaw history : Measure (Nat -> Symbol))
        {future | future 0 = symbol} ->
      (futureLaw (extendHistory history symbol) : Measure (Nat -> Symbol)) =
        ((futureLaw history : Measure (Nat -> Symbol))
          {future | future 0 = symbol})⁻¹ •
          Measure.map (fun future index => future (index + 1))
            ((futureLaw history : Measure (Nat -> Symbol)).restrict
              {future | future 0 = symbol})) :
    exists update :
        Quotient (Setoid.ker futureLaw) -> Symbol ->
          Quotient (Setoid.ker futureLaw),
      (forall history symbol,
        0 < (futureLaw history : Measure (Nat -> Symbol))
          {future | future 0 = symbol} ->
        update (Quotient.mk (Setoid.ker futureLaw) history) symbol =
          Quotient.mk (Setoid.ker futureLaw)
            (extendHistory history symbol)) /\
      forall history,
        ∀ᵐ symbol ∂Measure.map (fun future => future 0)
            (futureLaw history : Measure (Nat -> Symbol)),
          update (Quotient.mk (Setoid.ker futureLaw) history) symbol =
            Quotient.mk (Setoid.ker futureLaw)
              (extendHistory history symbol) := by
  let update :
      Quotient (Setoid.ker futureLaw) -> Symbol ->
        Quotient (Setoid.ker futureLaw) :=
    Quotient.lift
      (fun history symbol =>
        if positive : 0 < (futureLaw history : Measure (Nat -> Symbol))
            {future | future 0 = symbol} then
          Quotient.mk (Setoid.ker futureLaw)
            (extendHistory history symbol)
        else
          Quotient.mk (Setoid.ker futureLaw) history)
      (by
        intro history otherHistory sameLaw
        funext symbol
        have sameMeasure :
            (futureLaw history : Measure (Nat -> Symbol)) =
              (futureLaw otherHistory : Measure (Nat -> Symbol)) :=
          congrArg ProbabilityMeasure.toMeasure sameLaw
        have sameCylinder :
            (futureLaw history : Measure (Nat -> Symbol))
                {future | future 0 = symbol} =
              (futureLaw otherHistory : Measure (Nat -> Symbol))
                {future | future 0 = symbol} :=
          congrArg (fun law : Measure (Nat -> Symbol) =>
            law {future | future 0 = symbol}) sameMeasure
        by_cases positive :
            0 < (futureLaw history : Measure (Nat -> Symbol))
              {future | future 0 = symbol}
        · have otherPositive :
              0 < (futureLaw otherHistory : Measure (Nat -> Symbol))
                {future | future 0 = symbol} := by
            rwa [<- sameCylinder]
          simp only [dif_pos positive, dif_pos otherPositive]
          apply Quotient.sound
          apply ProbabilityMeasure.toMeasure_injective
          calc
            (futureLaw (extendHistory history symbol) :
                Measure (Nat -> Symbol)) =
                ((futureLaw history : Measure (Nat -> Symbol))
                  {future | future 0 = symbol})⁻¹ •
                  Measure.map (fun future index => future (index + 1))
                    ((futureLaw history : Measure (Nat -> Symbol)).restrict
                      {future | future 0 = symbol}) :=
              conditionedExtension history symbol positive
            _ = ((futureLaw otherHistory : Measure (Nat -> Symbol))
                  {future | future 0 = symbol})⁻¹ •
                  Measure.map (fun future index => future (index + 1))
                    ((futureLaw otherHistory : Measure (Nat -> Symbol)).restrict
                      {future | future 0 = symbol}) := by rw [sameMeasure]
            _ = (futureLaw (extendHistory otherHistory symbol) :
                Measure (Nat -> Symbol)) :=
              (conditionedExtension otherHistory symbol otherPositive).symm
        · have otherNotPositive :
              Not (0 < (futureLaw otherHistory : Measure (Nat -> Symbol))
                {future | future 0 = symbol}) := by
            rwa [<- sameCylinder]
          simp only [dif_neg positive, dif_neg otherNotPositive]
          exact Quotient.sound sameLaw)
  have computesOnPositive : forall history symbol,
      0 < (futureLaw history : Measure (Nat -> Symbol))
        {future | future 0 = symbol} ->
      update (Quotient.mk (Setoid.ker futureLaw) history) symbol =
        Quotient.mk (Setoid.ker futureLaw)
          (extendHistory history symbol) := by
    intro history symbol positive
    simp only [update, Quotient.lift_mk, dif_pos positive]
  refine ⟨update, computesOnPositive, ?_⟩
  intro history
  rw [ae_iff_of_countable]
  intro symbol positiveMarginal
  apply computesOnPositive history symbol
  apply bot_lt_iff_ne_bot.mpr
  intro cylinderZero
  apply positiveMarginal
  rw [Measure.map_apply (measurable_pi_apply 0)
    (MeasurableSet.singleton symbol)]
  have preimageCylinder :
      (fun future : Nat -> Symbol => future 0) ⁻¹' {symbol} =
        {future | future 0 = symbol} := by
    ext future
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  rw [preimageCylinder]
  exact cylinderZero

#print axioms unifilar_predictive_update

end D5.S3.ObserverMemory.ContextUpdates.PredictiveStateUnifilarUpdate
