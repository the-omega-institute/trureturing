/- GID: D5/S3/ObserverMemory/Prediction/FusionStateCardinality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FusionStateCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Surjections and a product injection bound fused-state cardinality. -/

import Mathlib.SetTheory.Cardinal.Finite

/- Library-search audit trail (2026-08-15):
   * Exact pinned-Mathlib hits: `Nat.card_le_card_of_surjective`,
     `Nat.card_le_card_of_injective`, and `Nat.card_prod` provide the four
     cardinal comparisons used below.
   * Loogle and LeanSearch found range-cardinality and paired-range component
     lemmas, but no declaration packaging the complete max/min bound.
   * A repository search found no declaration with the complete bound.
-/

namespace D5.S3.ObserverMemory.Prediction.FusionStateCardinality

/-- A finite fused state space lies above both component state counts and below
both the original state count and the product of the component counts. -/
theorem fusion_state_cardinality_bounds
    {Y Z1 Z2 Z12 : Type*} [Finite Y] [Finite Z1] [Finite Z2] [Finite Z12]
    (pi : Y -> Z12) (toFirst : Z12 -> Z1) (toSecond : Z12 -> Z2)
    (intoProduct : Z12 -> Z1 × Z2)
    (pi_surjective : Function.Surjective pi)
    (first_surjective : Function.Surjective toFirst)
    (second_surjective : Function.Surjective toSecond)
    (product_injective : Function.Injective intoProduct) :
    max (Nat.card Z1) (Nat.card Z2) <= Nat.card Z12 /\
      Nat.card Z12 <= min (Nat.card Y) (Nat.card Z1 * Nat.card Z2) := by
  constructor
  · exact max_le
      (Nat.card_le_card_of_surjective toFirst first_surjective)
      (Nat.card_le_card_of_surjective toSecond second_surjective)
  · apply le_min
    · exact Nat.card_le_card_of_surjective pi pi_surjective
    · simpa only [Nat.card_prod] using
        Nat.card_le_card_of_injective intoProduct product_injective

/-- The map hypotheses are jointly satisfiable on a concrete inhabited finite
carrier. -/
example :
    max (Nat.card Unit) (Nat.card Unit) <= Nat.card Unit /\
      Nat.card Unit <= min (Nat.card Unit) (Nat.card Unit * Nat.card Unit) := by
  apply fusion_state_cardinality_bounds
      (pi := id)
      (toFirst := id)
      (toSecond := id)
      (intoProduct := fun y : Unit => (y, y))
  · exact Function.surjective_id
  · exact Function.surjective_id
  · exact Function.surjective_id
  · intro a b _
    exact Subsingleton.elim a b

/-- The carrier used by the satisfiability witness is inhabited. -/
example : Unit := ()

end D5.S3.ObserverMemory.Prediction.FusionStateCardinality
