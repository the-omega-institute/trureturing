/- GID: D5/S3/ObserverMemory/Fusion/JointPredictionProductFullness
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/JointPredictionProductFullness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint prediction fills its product exactly when every pair of fibers meets. -/

import Mathlib.SetTheory.Cardinal.Finite

/- Library-search audit trail (2026-08-16):
   * Exact pinned-Mathlib hits: `Nat.bijective_iff_injective_and_card` turns
     injectivity plus equal finite cardinality into bijectivity, and
     `Nat.card_prod` evaluates the product cardinality.
   * Local smart-search queries returned no declarations; direct pinned-source
     search found the two exact cardinal building blocks above.
   * Loogle returned zero results for the shaped cardinality query.
     LeanSearch's `/api/search` endpoint returned HTTP 404.
   * Repository search found the adjacent fusion cardinality bounds, but no
     declaration equivalent to the three-way fullness criterion below. -/

namespace D5.S3.ObserverMemory.Fusion.JointPredictionProductFullness

/-- The states realizing one prediction value. -/
def predictionFiber {Y Z : Type*} (readout : Y -> Z) (value : Z) : Set Y :=
  {state | readout state = value}

/-- A joint prediction map is onto exactly when every pair of component fibers
meets; for an injective joint map between finite state spaces, this is also
equivalent to the fused state count attaining the product bound. -/
theorem joint_prediction_product_fullness_criterion
    {Y Z1 Z2 Z12 : Type*} [Finite Y] [Finite Z1] [Finite Z2] [Finite Z12]
    (realize : Y -> Z12) (first : Y -> Z1) (second : Y -> Z2)
    (joint : Z12 -> Z1 × Z2)
    (realize_surjective : Function.Surjective realize)
    (joint_injective : Function.Injective joint)
    (joint_realizes : forall state,
      joint (realize state) = (first state, second state)) :
    (Function.Surjective joint <->
      forall firstValue secondValue,
        (predictionFiber first firstValue ∩
          predictionFiber second secondValue).Nonempty) /\
    (Function.Surjective joint <->
      Nat.card Z12 = Nat.card Z1 * Nat.card Z2) := by
  constructor
  · constructor
    · intro joint_surjective firstValue secondValue
      obtain ⟨fused, hfused⟩ := joint_surjective (firstValue, secondValue)
      obtain ⟨state, hstate⟩ := realize_surjective fused
      have hvalues := joint_realizes state
      rw [hstate, hfused] at hvalues
      refine ⟨state, ?_, ?_⟩
      · exact (congrArg Prod.fst hvalues).symm
      · exact (congrArg Prod.snd hvalues).symm
    · intro fibers_meet pair
      obtain ⟨state, hfirst, hsecond⟩ := fibers_meet pair.1 pair.2
      refine ⟨realize state, ?_⟩
      rw [joint_realizes state, hfirst, hsecond]
  · constructor
    · intro joint_surjective
      have joint_bijective : Function.Bijective joint :=
        ⟨joint_injective, joint_surjective⟩
      have hcard :=
        (Nat.bijective_iff_injective_and_card joint).mp joint_bijective
      simpa only [Nat.card_prod] using hcard.2
    · intro hcard
      have product_card : Nat.card Z12 = Nat.card (Z1 × Z2) := by
        simpa only [Nat.card_prod] using hcard
      exact ((Nat.bijective_iff_injective_and_card joint).mpr
        ⟨joint_injective, product_card⟩).2

/-- The criterion's hypotheses and all three equivalent conditions are
simultaneously realized on a one-state system. -/
example :
    let first : Unit -> Unit := id
    let second : Unit -> Unit := id
    let joint : Unit -> Unit × Unit := fun _ => ((), ())
    (Function.Surjective joint <->
      forall firstValue secondValue,
        (predictionFiber first firstValue ∩
          predictionFiber second secondValue).Nonempty) /\
    (Function.Surjective joint <->
      Nat.card Unit = Nat.card Unit * Nat.card Unit) := by
  dsimp
  apply joint_prediction_product_fullness_criterion (realize := id)
  · exact Function.surjective_id
  · intro left right _
    exact Subsingleton.elim left right
  · intro state
    cases state
    rfl

end D5.S3.ObserverMemory.Fusion.JointPredictionProductFullness
