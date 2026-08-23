/- GID: D5/S3/Observer/Prediction/FiniteEquivalenceDescent
   generality: G
   mirror-B: D5/B/S3/Observer/Prediction/FiniteEquivalenceDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite equivalence refinement stabilizes within its quotient-class budget. -/

import D5.S3.Observer.Prediction.StableDepthCardinalityBounds

/- Library-search audit trail (2026-08-23):
   * Exact repository hits `finite_relation_zero` and `finite_relation_succ` construct the
     source's finite descent, and both are applied below.
   * Exact repository hit `finite_history_stability` proves permanent stabilization of the
     canonical finite-future relation and is applied below.
   * Exact repository hit `stable_depth_runtime_and_token_bounds` proves both sharp quotient
     class bounds and is applied below to the canonical quotient readout.
   * Pinned Mathlib's `Quotient.eq`, `Quotient.mk_surjective`, and `Fintype.ofSurjective`
     provide the relation and finite-quotient bridges. No exact theorem packaging every clause
     for an arbitrary input setoid was found in the repository or pinned Mathlib. -/

noncomputable section

namespace D5.S3.Observer.Prediction.FiniteEquivalenceDescent

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteHistoryStability
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.Observer.Prediction.StableDepthCardinalityBounds
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The canonical finite refinement of an equivalence relation is its finite-iterate
intersection. Its least adjacent-stability depth reaches the all-future relation and is bounded
by the number of quotient classes created during refinement. -/
theorem finite_equivalence_descent_and_stability_bound
    {Y : Type*} [Fintype Y] (relation : Setoid Y) (update : Y -> Y) :
    finiteFutureRelation update (Quotient.mk relation) 0 =
        {pair | relation pair.1 pair.2} /\
    (forall m, finiteFutureRelation update (Quotient.mk relation) (m + 1) =
      {pair | relation pair.1 pair.2 /\
        (update pair.1, update pair.2) ∈
          finiteFutureRelation update (Quotient.mk relation) m}) /\
    (forall m, finiteFutureRelation update (Quotient.mk relation) m =
      ⋂ k : Fin (m + 1),
        {pair | relation ((update^[k.1]) pair.1) ((update^[k.1]) pair.2)}) /\
    ((finiteFutureRelation update (Quotient.mk relation)
          (observationStabilityDepth update (Quotient.mk relation)) =
        finiteFutureRelation update (Quotient.mk relation)
          (observationStabilityDepth update (Quotient.mk relation) + 1)) /\
      forall n, finiteFutureRelation update (Quotient.mk relation) n =
          finiteFutureRelation update (Quotient.mk relation) (n + 1) ->
        observationStabilityDepth update (Quotient.mk relation) <= n) /\
    (forall n, observationStabilityDepth update (Quotient.mk relation) <= n ->
      finiteFutureRelation update (Quotient.mk relation) n =
        infiniteFutureRelation update (Quotient.mk relation)) /\
    observationStabilityDepth update (Quotient.mk relation) <=
      infiniteObservationClassCount update (Quotient.mk relation) -
        Nat.card (Quotient relation) /\
    infiniteObservationClassCount update (Quotient.mk relation) -
        Nat.card (Quotient relation) <=
      Fintype.card Y - Nat.card (Quotient relation) := by
  classical
  letI : Fintype (Quotient relation) :=
    Fintype.ofSurjective (Quotient.mk relation) Quotient.mk_surjective
  have hzero : finiteFutureRelation update (Quotient.mk relation) 0 =
      {pair | relation pair.1 pair.2} := by
    rw [finite_relation_zero]
    ext pair
    exact Quotient.eq
  have hsucc : forall m,
      finiteFutureRelation update (Quotient.mk relation) (m + 1) =
        {pair | relation pair.1 pair.2 /\
          (update pair.1, update pair.2) ∈
            finiteFutureRelation update (Quotient.mk relation) m} := by
    intro m
    rw [finite_relation_succ]
    ext pair
    exact and_congr Quotient.eq Iff.rfl
  have hintersection : forall m,
      finiteFutureRelation update (Quotient.mk relation) m =
        ⋂ k : Fin (m + 1),
          {pair | relation ((update^[k.1]) pair.1) ((update^[k.1]) pair.2)} := by
    intro m
    ext pair
    simp only [finiteFutureRelation, observedAt, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h k
      exact Quotient.exact (h k.1 (Nat.le_of_lt_succ k.isLt))
    · intro h k hk
      exact Quotient.sound (h ⟨k, Nat.lt_succ_of_le hk⟩)
  have hhistory := finite_history_stability update (Quotient.mk relation)
  have hadjacent : finiteFutureRelation update (Quotient.mk relation)
        (observationStabilityDepth update (Quotient.mk relation)) =
      finiteFutureRelation update (Quotient.mk relation)
        (observationStabilityDepth update (Quotient.mk relation) + 1) := by
    calc
      finiteFutureRelation update (Quotient.mk relation)
          (observationStabilityDepth update (Quotient.mk relation)) =
          infiniteFutureRelation update (Quotient.mk relation) := hhistory.2.2.1
      _ = finiteFutureRelation update (Quotient.mk relation)
          (observationStabilityDepth update (Quotient.mk relation) + 1) :=
        (hhistory.2.2.2.1 _ (Nat.le_succ _)).symm
  have hsetoid_rel_iff : forall m x y,
      observationSetoid update (Quotient.mk relation) m x y <->
        (x, y) ∈ finiteFutureRelation update (Quotient.mk relation) m := by
    intro m x y
    constructor
    · intro h k hk
      simpa only [futureReadoutWord, observedAt] using
        congrFun h (show Fin (m + 1) from ⟨k, Nat.lt_succ_of_le hk⟩)
    · intro h
      funext k
      simpa only [futureReadoutWord, observedAt] using
        h k (Nat.le_of_lt_succ k.isLt)
  have hsetoid_iff_relation : forall m n,
      observationSetoid update (Quotient.mk relation) m =
          observationSetoid update (Quotient.mk relation) n <->
        finiteFutureRelation update (Quotient.mk relation) m =
          finiteFutureRelation update (Quotient.mk relation) n := by
    intro m n
    constructor
    · intro hsetoid
      ext pair
      rw [← hsetoid_rel_iff, ← hsetoid_rel_iff, hsetoid]
    · intro hrelation
      apply Setoid.ext
      intro x y
      rw [hsetoid_rel_iff, hsetoid_rel_iff, hrelation]
  have hminimal : forall n,
      finiteFutureRelation update (Quotient.mk relation) n =
          finiteFutureRelation update (Quotient.mk relation) (n + 1) ->
        observationStabilityDepth update (Quotient.mk relation) <= n := by
    intro n hn
    unfold observationStabilityDepth
    apply Nat.sInf_le
    exact (hsetoid_iff_relation n (n + 1)).2 hn
  have hbounds :
      observationStabilityDepth update (Quotient.mk relation) <=
          infiniteObservationClassCount update (Quotient.mk relation) -
            Nat.card (Quotient relation) /\
        infiniteObservationClassCount update (Quotient.mk relation) -
            Nat.card (Quotient relation) <=
          Fintype.card Y - Nat.card (Quotient relation) := by
    by_cases hnonempty : Nonempty Y
    · letI : Nonempty Y := hnonempty
      have hfull :
          (observationStabilityDepth update (Quotient.mk relation) <=
              infiniteObservationClassCount update (Quotient.mk relation) -
                Fintype.card (Quotient relation) /\
            infiniteObservationClassCount update (Quotient.mk relation) -
                Fintype.card (Quotient relation) <=
              Fintype.card Y - Fintype.card (Quotient relation)) /\
          (forall (Sigma : Type) [Fintype Sigma] [Nonempty Sigma] (L : Nat)
            (tokenUpdate : (Fin L -> Sigma) -> (Fin L -> Sigma))
            (tokenReadout : (Fin L -> Sigma) -> Sigma),
            Function.Surjective tokenReadout ->
              observationStabilityDepth tokenUpdate tokenReadout <=
                Fintype.card Sigma ^ L - Fintype.card Sigma) :=
        stable_depth_runtime_and_token_bounds update
          (Quotient.mk relation) Quotient.mk_surjective
      have h := hfull.1
      simpa only [Nat.card_eq_fintype_card] using h
    · letI : IsEmpty Y := ⟨fun y => hnonempty ⟨y⟩⟩
      have hdepthBound := hhistory.2.2.2.2.1
      have hstableCount : observationClassCount update (Quotient.mk relation)
          (observationStabilityDepth update (Quotient.mk relation)) = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        infer_instance
      have hinitialCount : observationClassCount update (Quotient.mk relation) 0 = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        infer_instance
      have hdepth : observationStabilityDepth update (Quotient.mk relation) = 0 := by
        omega
      simp [hdepth, infiniteObservationClassCount]
  exact ⟨hzero, hsucc, hintersection, ⟨hadjacent, hminimal⟩,
    hhistory.2.2.2.1, hbounds.1, hbounds.2⟩

#print axioms finite_equivalence_descent_and_stability_bound

end D5.S3.Observer.Prediction.FiniteEquivalenceDescent
