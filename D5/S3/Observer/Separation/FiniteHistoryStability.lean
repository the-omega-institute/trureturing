/- GID: D5/S3/Observer/Separation/FiniteHistoryStability
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/FiniteHistoryStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite observation histories stabilize and their class growth is bounded by the finite carrier. -/

import D5.S3.Observer.Separation.FiniteFutureCongruence
import D5.S3.Observer.Separation.FiniteObservationRefinementBound

/- Library-search audit trail (2026-08-21):
   * Exact repository hits `infinite_relation_stabilizes` and
     `finite_relation_eq_infinite_of_stable` are imported and applied through
     the original iteration/readout relations.
   * Exact repository hit
     `finite_observation_refinement_and_stability_bound` is applied after a
     private corestriction of an arbitrary readout to `Set.range readout`.
   * The corestriction bridges finite words, stable depths, and quotient counts
     back to the original readout; no stronger source hypothesis is added.
   * Pinned Mathlib ingredients used by the imported result are
     `Fintype.bijective_iff_surjective_and_card`, `Fintype.card_le_of_surjective`,
     and `Nat.sInf_mem`.
-/

noncomputable section

namespace D5.S3.Observer.Separation.FiniteHistoryStability

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift

private def rangeReadout {X Q : Type*} (readout : X -> Q) : X -> Set.range readout :=
  fun x => ⟨readout x, ⟨x, rfl⟩⟩

private theorem rangeReadout_surjective {X Q : Type*} (readout : X -> Q) :
    Function.Surjective (rangeReadout readout) := by
  intro value
  obtain ⟨x, hx⟩ := value.property
  refine ⟨x, ?_⟩
  exact Subtype.ext (by simpa [rangeReadout] using hx)

private theorem finite_relation_rangeReadout {X Q : Type*}
    (update : X -> X) (readout : X -> Q) (m : Nat) :
    finiteFutureRelation update (rangeReadout readout) m =
      finiteFutureRelation update readout m := by
  ext pair
  constructor
  · intro h k hk
    exact congrArg Subtype.val (h k hk)
  · intro h k hk
    exact Subtype.ext (h k hk)

private theorem infinite_relation_rangeReadout {X Q : Type*}
    (update : X -> X) (readout : X -> Q) :
    infiniteFutureRelation update (rangeReadout readout) =
      infiniteFutureRelation update readout := by
  ext pair
  constructor
  · intro h k
    exact congrArg Subtype.val (h k)
  · intro h k
    exact Subtype.ext (h k)

private theorem setoid_rangeReadout {X Q : Type*}
    (update : X -> X) (readout : X -> Q) (m : Nat) :
    observationSetoid update (rangeReadout readout) m =
      observationSetoid update readout m := by
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    funext k
    exact congrArg Subtype.val (congrFun h k)
  · intro h
    funext k
    exact Subtype.ext (congrFun h k)

private theorem class_count_rangeReadout {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) (m : Nat) :
    observationClassCount update (rangeReadout readout) m =
      observationClassCount update readout m := by
  let hquot : Quotient (observationSetoid update (rangeReadout readout) m) =
      Quotient (observationSetoid update readout m) :=
    congrArg Quotient (setoid_rangeReadout update readout m)
  exact Fintype.card_congr (Equiv.cast hquot)

private theorem initial_class_count_rangeReadout {X Q : Type*} [Fintype X]
    (update : X -> X) (readout : X -> Q) [Fintype (Set.range readout)] :
    observationClassCount update (rangeReadout readout) 0 =
      Fintype.card (Set.range readout) := by
  have hword : Function.Surjective
      (futureReadoutWord update (rangeReadout readout) 0) := by
    intro word
    rcases word 0 |>.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    funext k
    have hk : k = (0 : Fin 1) := Fin.eq_zero k
    subst k
    apply Subtype.ext
    simpa [futureReadoutWord, rangeReadout] using hx
  let rangeEquiv : Set.range (futureReadoutWord update
      (rangeReadout readout) 0) ≃ (Fin 1 -> Set.range readout) :=
    Equiv.ofBijective Subtype.val
      ⟨Subtype.val_injective, by
        intro word
        rcases hword word with ⟨x, hx⟩
        exact ⟨⟨word, x, hx⟩, rfl⟩⟩
  have hcard := Fintype.card_congr
    ((finiteWordRangeEquiv update (rangeReadout readout) 0).trans rangeEquiv)
  simpa [observationClassCount] using hcard

private theorem stable_depth_rangeReadout {X Q : Type*}
    (update : X -> X) (readout : X -> Q) :
    observationStabilityDepth update (rangeReadout readout) =
      observationStabilityDepth update readout := by
  unfold observationStabilityDepth
  congr 1
  ext m
  change (observationSetoid update (rangeReadout readout) m =
      observationSetoid update (rangeReadout readout) (m + 1)) ↔
    (observationSetoid update readout m =
      observationSetoid update readout (m + 1))
  rw [setoid_rangeReadout, setoid_rangeReadout]

private theorem setoid_relation_iff {X Q : Type*}
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

private theorem setoid_eq_of_relation_eq {X Q : Type*}
    (update : X -> X) (readout : X -> Q) (m n : Nat)
    (hrel : finiteFutureRelation update readout m =
      finiteFutureRelation update readout n) :
    observationSetoid update readout m = observationSetoid update readout n := by
  apply Setoid.ext
  intro x y
  rw [setoid_relation_iff, setoid_relation_iff, hrel]

private theorem relation_eq_of_setoid_eq {X Q : Type*}
    (update : X -> X) (readout : X -> Q) (m n : Nat)
    (hsetoid : observationSetoid update readout m =
      observationSetoid update readout n) :
    finiteFutureRelation update readout m =
      finiteFutureRelation update readout n := by
  ext pair
  rw [← setoid_relation_iff, ← setoid_relation_iff, hsetoid]

private theorem empty_depth_zero {X Q : Type*} [Fintype X] [IsEmpty X]
    (update : X -> X) (readout : X -> Q) :
    observationStabilityDepth update readout = 0 := by
  unfold observationStabilityDepth
  have hset : {m | observationSetoid update readout m =
      observationSetoid update readout (m + 1)} = Set.univ := by
    ext m
    have hrel : observationSetoid update readout m =
        observationSetoid update readout (m + 1) := by
      apply Setoid.ext
      intro x y
      exact isEmptyElim x
    simp [hrel]
  rw [hset]
  simp

private theorem empty_class_count_zero {X Q : Type*} [Fintype X] [IsEmpty X]
    (update : X -> X) (readout : X -> Q) (m : Nat) :
    observationClassCount update readout m = 0 := by
  unfold observationClassCount
  apply Fintype.card_eq_zero_iff.mpr
  infer_instance

/- The finite-history theorem is stated on the source's original readout.
   Range corestriction is used only to discharge the existing surjective-readout
   package, then every clause is transported back to the original carrier. -/
theorem finite_history_stability
    {X Q : Type*} [Fintype X] (update : X -> X) (readout : X -> Q) :
    (forall m, finiteFutureRelation update readout (m + 1) <=
      finiteFutureRelation update readout m) /\
    (forall m, observationClassCount update readout m <=
      observationClassCount update readout (m + 1)) /\
    finiteFutureRelation update readout
        (observationStabilityDepth update readout) =
      infiniteFutureRelation update readout /\
    (forall n, observationStabilityDepth update readout <= n ->
      finiteFutureRelation update readout n =
        infiniteFutureRelation update readout) /\
    observationStabilityDepth update readout <=
      observationClassCount update readout
          (observationStabilityDepth update readout) -
        observationClassCount update readout 0 /\
    observationClassCount update readout
          (observationStabilityDepth update readout) -
        observationClassCount update readout 0 <=
      Fintype.card X - observationClassCount update readout 0 := by
  classical
  by_cases hnonempty : Nonempty X
  · letI : Nonempty X := hnonempty
    letI : Fintype (Set.range readout) := Fintype.ofFinite _
    let ranged := rangeReadout readout
    have hgeneral := finite_observation_refinement_and_stability_bound
      update ranged (rangeReadout_surjective readout)
    have hrel := hgeneral.1
    have hcount := hgeneral.2.1
    have hstable := hgeneral.2.2.1.1
    have hminimal := hgeneral.2.2.1.2
    have hdepth := hgeneral.2.2.2.1
    have hbound := hgeneral.2.2.2.2
    have hdepth_eq : observationStabilityDepth update ranged =
        observationStabilityDepth update readout :=
      stable_depth_rangeReadout update readout
    have hstable_relation : finiteFutureRelation update readout
        (observationStabilityDepth update readout) =
        infiniteFutureRelation update readout := by
      have hstable_ranged : finiteFutureRelation update ranged
          (observationStabilityDepth update ranged) =
          infiniteFutureRelation update ranged := by
        have hstable_finite := relation_eq_of_setoid_eq update ranged
          (observationStabilityDepth update ranged)
          (observationStabilityDepth update ranged + 1) hstable
        exact finite_relation_eq_infinite_of_stable update ranged
          (observationStabilityDepth update ranged) hstable_finite
      calc
        finiteFutureRelation update readout
            (observationStabilityDepth update readout) =
            finiteFutureRelation update ranged
              (observationStabilityDepth update readout) :=
          (finite_relation_rangeReadout update readout
            (observationStabilityDepth update readout)).symm
        _ = finiteFutureRelation update ranged
              (observationStabilityDepth update ranged) := by
          rw [hdepth_eq]
        _ = infiniteFutureRelation update ranged := hstable_ranged
        _ = infiniteFutureRelation update readout :=
          infinite_relation_rangeReadout update readout
    have hcount_transport : forall m,
        observationClassCount update ranged m =
          observationClassCount update readout m := by
      intro m
      exact class_count_rangeReadout update readout m
    refine ⟨?_, ?_, hstable_relation, ?_, ?_, ?_⟩
    · intro m pair hp k hk
      exact hp k (Nat.le_trans hk (Nat.le_succ m))
    · intro m
      rw [← hcount_transport m, ← hcount_transport (m + 1)]
      exact hcount m
    · intro n hn
      apply le_antisymm
      · intro pair hp
        rw [← hstable_relation]
        intro k hk
        exact hp k (Nat.le_trans hk hn)
      · intro pair hp k hk
        exact hp k
    · rw [← hcount_transport (observationStabilityDepth update readout),
      ← hcount_transport 0]
      have hdepth' := hdepth
      rw [hdepth_eq] at hdepth'
      simpa only [hcount_transport] using hdepth'
    · rw [← hcount_transport (observationStabilityDepth update readout),
      ← hcount_transport 0]
      have hbound' := hbound
      rw [hdepth_eq] at hbound'
      have hinitial := initial_class_count_rangeReadout update readout
      rw [← hinitial] at hbound'
      exact hbound'
  · letI : IsEmpty X := ⟨fun x => hnonempty ⟨x⟩⟩
    have hdepth : observationStabilityDepth update readout = 0 :=
      empty_depth_zero update readout
    have hcount : forall m, observationClassCount update readout m = 0 := by
      intro m
      exact empty_class_count_zero update readout m
    have hstable : forall m, finiteFutureRelation update readout m =
        infiniteFutureRelation update readout := by
      intro m
      exact Subsingleton.elim _ _
    rw [hdepth]
    refine ⟨?_, ?_, hstable 0, ?_, ?_, ?_⟩
    · intro m pair hp k hk
      exact hp k (Nat.le_trans hk (Nat.le_succ m))
    · intro m
      rw [hcount m, hcount (m + 1)]
    · intro n hn
      exact hstable n
    · simp
    · simp

#print axioms finite_history_stability

end D5.S3.Observer.Separation.FiniteHistoryStability
