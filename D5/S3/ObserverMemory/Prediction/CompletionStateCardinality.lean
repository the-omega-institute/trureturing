/- GID: D5/S3/ObserverMemory/Prediction/CompletionStateCardinality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/CompletionStateCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A surjective refinement map makes completed-state cardinality monotone. -/

import Mathlib.Data.Fintype.Card

/- Library-search audit trail (2026-08-16):
   * Exact pinned-Mathlib and Loogle hit: `Fintype.card_le_of_surjective` has
     precisely the required finite-cardinality comparison and is applied below.
   * Repository searches found the same lemma used inside entropy and fusion
     bounds, but no standalone completed-state refinement declaration.
   * LeanSearch's public search endpoint returned HTTP 405 and 422, so it
     supplied no additional result.
-/

namespace D5.S3.ObserverMemory.Prediction.CompletionStateCardinality

/-- A surjective map from refined completed states onto coarse completed states
shows that observation refinement cannot decrease the number of states. -/
theorem completion_state_cardinality_mono
    {Fine Coarse : Type*} [Fintype Fine] [Fintype Coarse]
    (forget : Fine -> Coarse) (forget_surjective : Function.Surjective forget) :
    Fintype.card Coarse <= Fintype.card Fine :=
  Fintype.card_le_of_surjective forget forget_surjective

end D5.S3.ObserverMemory.Prediction.CompletionStateCardinality
