/- GID: D5/S3/Observer/Prediction/FiniteStabilityClassBound
   generality: G
   mirror-B: D5/B/S3/Observer/Prediction/FiniteStabilityClassBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The least finite-future stability depth obeys the exact quotient-class bound. -/

import D5.S3.Observer.Prediction.StableDepthCardinalityBounds

/- Library-search audit trail (2026-08-25):
   * Exact repository hit `finite_history_stability` proves stable finite-relation equality
     and the two finite class-growth bounds; it is applied directly below.
   * Exact repository hit `StableDepthCardinalityBounds` supplies the canonical complete-future
     setoid and class count, which are imported rather than redeclared.
   * Exact repository hit `finite_equivalence_descent_and_stability_bound` confirms the least
     adjacent-stability formulation used publicly here.
   * Exact pinned-Mathlib hit `Setoid.quotientKerEquivRange` canonically identifies the initial
     kernel quotient with the realized readout range and is applied directly below. -/

noncomputable section

namespace D5.S3.Observer.Prediction.FiniteStabilityClassBound

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteHistoryStability
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.Observer.Prediction.StableDepthCardinalityBounds
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem observation_setoid_rel_iff {X Q : Type*}
    (update : X -> X) (readout : X -> Q) (m : Nat) (x y : X) :
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

private theorem infinite_observation_setoid_rel_iff {X Q : Type*}
    (update : X -> X) (readout : X -> Q) (x y : X) :
    infiniteObservationSetoid update readout x y <->
      (x, y) ∈ infiniteFutureRelation update readout := by
  constructor
  · intro h k
    exact congrFun h k
  · intro h
    funext k
    exact h k

private theorem observation_setoid_eq_iff_finite_relation_eq {X Q : Type*}
    (update : X -> X) (readout : X -> Q) (m n : Nat) :
    observationSetoid update readout m = observationSetoid update readout n <->
      finiteFutureRelation update readout m =
        finiteFutureRelation update readout n := by
  constructor
  · intro hsetoid
    ext pair
    rw [← observation_setoid_rel_iff, ← observation_setoid_rel_iff, hsetoid]
  · intro hrelation
    apply Setoid.ext
    intro x y
    rw [observation_setoid_rel_iff, observation_setoid_rel_iff, hrelation]

private theorem stable_setoid_eq_infinite {X Q : Type*} [Finite X]
    (update : X -> X) (readout : X -> Q) :
    observationSetoid update readout
        (observationStabilityDepth update readout) =
      infiniteObservationSetoid update readout := by
  letI := Fintype.ofFinite X
  have hstable := (finite_history_stability update readout).2.2.1
  apply Setoid.ext
  intro x y
  rw [observation_setoid_rel_iff, infinite_observation_setoid_rel_iff, hstable]

private theorem stable_count_eq_infinite {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) :
    observationClassCount update readout
        (observationStabilityDepth update readout) =
      infiniteObservationClassCount update readout := by
  exact Fintype.card_congr
    (Equiv.cast (congrArg Quotient (stable_setoid_eq_infinite update readout)))

private theorem initial_count_eq_kernel_quotient {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) :
    observationClassCount update readout 0 =
      Nat.card (Quotient (Setoid.ker readout)) := by
  letI : Fintype (Quotient (Setoid.ker readout)) := Fintype.ofFinite _
  have hsetoid : observationSetoid update readout 0 = Setoid.ker readout := by
    apply Setoid.ext
    intro x y
    constructor
    · intro h
      simpa [futureReadoutWord, observedAt] using congrFun h (0 : Fin 1)
    · intro h
      funext k
      have hk : k = (0 : Fin 1) := Fin.eq_zero k
      subst k
      simpa [futureReadoutWord, observedAt] using h
  have hcard := Fintype.card_congr
    (Equiv.cast (congrArg Quotient hsetoid))
  simpa only [observationClassCount, Nat.card_eq_fintype_card] using hcard

private theorem quotient_kernel_card_eq_range {X Q : Type*} (readout : X -> Q) :
    Nat.card (Quotient (Setoid.ker readout)) = Nat.card (Set.range readout) := by
  exact Nat.card_congr (Setoid.quotientKerEquivRange readout)

private theorem stability_depth_minimal {X Q : Type*}
    (update : X -> X) (readout : X -> Q) :
    forall n, finiteFutureRelation update readout n =
        finiteFutureRelation update readout (n + 1) ->
      observationStabilityDepth update readout <= n := by
  intro n hn
  unfold observationStabilityDepth
  apply Nat.sInf_le
  exact (observation_setoid_eq_iff_finite_relation_eq
    update readout n (n + 1)).2 hn

/-- The least adjacent-stability depth of the finite-future kernel tower reaches the complete
future kernel. Its depth is bounded by the number of new complete-future quotient classes, and
that class gain is bounded by the gap between the state carrier and the realized readout image. -/
theorem finite_stability_class_bound
    {X Q : Type*} [Fintype X] (update : X -> X) (readout : X -> Q) :
    let m := observationStabilityDepth update readout
    ((finiteFutureRelation update readout m =
          finiteFutureRelation update readout (m + 1) /\
        finiteFutureRelation update readout m =
          infiniteFutureRelation update readout /\
        finiteFutureRelation update readout (m + 1) =
          infiniteFutureRelation update readout) /\
      (forall n, finiteFutureRelation update readout n =
          finiteFutureRelation update readout (n + 1) -> m <= n)) /\
    m <= infiniteObservationClassCount update readout -
        Nat.card (Quotient (Setoid.ker readout)) /\
    infiniteObservationClassCount update readout -
        Nat.card (Quotient (Setoid.ker readout)) <=
      Fintype.card X - Nat.card (Set.range readout) := by
  classical
  dsimp
  have hhistory := finite_history_stability update readout
  have hstable := hhistory.2.2.1
  have hnext := hhistory.2.2.2.1
    (observationStabilityDepth update readout + 1) (Nat.le_succ _)
  have hadjacent : finiteFutureRelation update readout
        (observationStabilityDepth update readout) =
      finiteFutureRelation update readout
        (observationStabilityDepth update readout + 1) :=
    hstable.trans hnext.symm
  have hfirst := hhistory.2.2.2.2.1
  have hsecond := hhistory.2.2.2.2.2
  rw [stable_count_eq_infinite update readout,
    initial_count_eq_kernel_quotient update readout] at hfirst hsecond
  have hquotientRange := quotient_kernel_card_eq_range readout
  refine ⟨⟨⟨hadjacent, hstable, hnext⟩,
    stability_depth_minimal update readout⟩, hfirst, ?_⟩
  calc
    infiniteObservationClassCount update readout -
          Nat.card (Quotient (Setoid.ker readout)) <=
        Fintype.card X - Nat.card (Quotient (Setoid.ker readout)) := hsecond
    _ = Fintype.card X - Nat.card (Set.range readout) :=
      congrArg (fun count => Fintype.card X - count) hquotientRange

#print axioms finite_stability_class_bound

end D5.S3.Observer.Prediction.FiniteStabilityClassBound
