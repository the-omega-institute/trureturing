/- GID: D5/S3/Observer/Prediction/StableDepthCardinalityBounds
   generality: G
   mirror-B: D5/B/S3/Observer/Prediction/StableDepthCardinalityBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stable prediction depth is bounded by the available future quotient classes. -/

import D5.S3.Observer.Separation.FiniteHistoryStability
import Mathlib.Data.Fintype.EquivFin

/- Library-search audit trail (2026-08-23):
   * Exact repository hit `finite_observation_refinement_and_stability_bound` proves the sharp
     growth budget for the source's least adjacent-stability depth and is applied below.
   * Exact repository hit `finite_history_stability` identifies the stable finite relation with
     the infinite-future relation and is applied below.
   * The canonical Observer primitives for future readout words, finite and infinite relations,
     class counts, and least stability depth are imported rather than redeclared.
   * No repository theorem exposed the infinite-future quotient count or the finite token-carrier
     specialization. Pinned Mathlib's `Fintype.card_congr` supplies the two quotient bridges. -/

noncomputable section

namespace D5.S3.Observer.Prediction.StableDepthCardinalityBounds

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.Observer.Separation.FiniteHistoryStability
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Equality of the complete future readout sequences. -/
def infiniteObservationSetoid {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :
    Setoid Y :=
  Setoid.ker (fun y k => observedAt update readout k y)

noncomputable instance infiniteObservationQuotientFintype
    {Y O : Type*} [Fintype Y] (update : Y -> Y) (readout : Y -> O) :
    Fintype (Quotient (infiniteObservationSetoid update readout)) :=
  by
    classical
    exact Fintype.ofSurjective (Quotient.mk _) Quotient.mk_surjective

/-- Number of state classes distinguished by the complete future readout. -/
def infiniteObservationClassCount {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) : Nat :=
  Fintype.card (Quotient (infiniteObservationSetoid update readout))

private theorem observation_setoid_rel_iff {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) (x y : Y) :
    observationSetoid update readout m x y <->
      (x, y) ∈ finiteFutureRelation update readout m := by
  constructor
  · intro h k hk
    simpa only [futureReadoutWord, observedAt] using
      congrFun h (show Fin (m + 1) from ⟨k, Nat.lt_succ_of_le hk⟩)
  · intro h
    funext k
    simpa only [futureReadoutWord, observedAt] using
      h k (Nat.le_of_lt_succ k.isLt)

private theorem infinite_observation_setoid_rel_iff {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (x y : Y) :
    infiniteObservationSetoid update readout x y <->
      (x, y) ∈ infiniteFutureRelation update readout := by
  constructor
  · intro h k
    exact congrFun h k
  · intro h
    funext k
    exact h k

private theorem stable_setoid_eq_infinite {Y O : Type*} [Finite Y]
    (update : Y -> Y) (readout : Y -> O) :
    observationSetoid update readout
        (observationStabilityDepth update readout) =
      infiniteObservationSetoid update readout := by
  letI := Fintype.ofFinite Y
  have hstable := (finite_history_stability update readout).2.2.1
  apply Setoid.ext
  intro x y
  rw [observation_setoid_rel_iff, infinite_observation_setoid_rel_iff, hstable]

private theorem stable_count_eq_infinite {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) :
    observationClassCount update readout
        (observationStabilityDepth update readout) =
      infiniteObservationClassCount update readout := by
  exact Fintype.card_congr
    (Equiv.cast (congrArg Quotient (stable_setoid_eq_infinite update readout)))

private theorem initial_class_count {Y O : Type*} [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    observationClassCount update readout 0 = Fintype.card O := by
  have hword : Function.Surjective (futureReadoutWord update readout 0) := by
    intro word
    rcases hreadout (word 0) with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    funext k
    have hk : k = (0 : Fin 1) := Fin.eq_zero k
    subst k
    simpa [futureReadoutWord] using hy
  let rangeEquiv : Set.range (futureReadoutWord update readout 0) ≃
      (Fin 1 -> O) :=
    Equiv.ofBijective Subtype.val
      ⟨Subtype.val_injective, by
        intro word
        rcases hword word with ⟨y, hy⟩
        exact ⟨⟨word, y, hy⟩, rfl⟩⟩
  have hcard := Fintype.card_congr
    ((finiteWordRangeEquiv update readout 0).trans rangeEquiv)
  simpa [observationClassCount] using hcard

private theorem stable_depth_cardinality_bounds
    {Y O : Type*} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    observationStabilityDepth update readout <=
        infiniteObservationClassCount update readout - Fintype.card O /\
      infiniteObservationClassCount update readout - Fintype.card O <=
        Fintype.card Y - Fintype.card O := by
  have hgeneral := finite_observation_refinement_and_stability_bound
    update readout hreadout
  have hdepth := hgeneral.2.2.2.1
  have hbound := hgeneral.2.2.2.2
  rw [stable_count_eq_infinite update readout,
    initial_class_count update readout hreadout] at hdepth hbound
  exact ⟨hdepth, hbound⟩

/-- The least stable prediction depth is bounded by the number of new complete-future classes.
For a minimal length-`L` token runtime, the state carrier is exactly `Fin L -> Sigma` and the
surjective readout has token alphabet `Sigma`, giving the stated vocabulary bound. -/
theorem stable_depth_runtime_and_token_bounds
    {Y O : Type*} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    (observationStabilityDepth update readout <=
        infiniteObservationClassCount update readout - Fintype.card O /\
      infiniteObservationClassCount update readout - Fintype.card O <=
        Fintype.card Y - Fintype.card O) /\
    (forall (Sigma : Type*) [Fintype Sigma] [Nonempty Sigma] (L : Nat)
      (tokenUpdate : (Fin L -> Sigma) -> (Fin L -> Sigma))
      (tokenReadout : (Fin L -> Sigma) -> Sigma),
      Function.Surjective tokenReadout ->
        observationStabilityDepth tokenUpdate tokenReadout <=
          Fintype.card Sigma ^ L - Fintype.card Sigma) := by
  constructor
  · exact stable_depth_cardinality_bounds update readout hreadout
  · intro Sigma _ _ L tokenUpdate tokenReadout htoken
    have htokenBounds := stable_depth_cardinality_bounds
      tokenUpdate tokenReadout htoken
    calc
      observationStabilityDepth tokenUpdate tokenReadout <=
          Fintype.card (Fin L -> Sigma) - Fintype.card Sigma :=
        le_trans htokenBounds.1 htokenBounds.2
      _ = Fintype.card Sigma ^ L - Fintype.card Sigma := by
        simp

#print axioms stable_depth_runtime_and_token_bounds

end D5.S3.Observer.Prediction.StableDepthCardinalityBounds
