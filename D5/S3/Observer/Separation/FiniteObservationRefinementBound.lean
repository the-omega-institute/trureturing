/- GID: D5/S3/Observer/Separation/FiniteObservationRefinementBound
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/FiniteObservationRefinementBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite observation classes refine monotonically and stabilize within the sharp bound. -/

import D5.S3.Observer.Separation.FiniteFutureCongruence
import D5.S3.ObserverMemory.Refinement.GradedPredictionShift
import Mathlib.Data.Fintype.EquivFin

/- Library-search audit trail (2026-08-17):
   * Repository search found the exact finite-stabilization prerequisite
     `infinite_relation_stabilizes`; it is imported and applied below.
   * Pinned Mathlib and Loogle found `Fintype.bijective_iff_surjective_and_card`,
     `Fintype.card_le_of_surjective`, and `Nat.sInf_mem`; all are applied below.
   * Repository search found the existing finite prediction quotient and its forgetful map,
     which are reused. No repository or pinned-Mathlib theorem packages all four clauses.
   * LeanSearch's shaped API query returned HTTP 404 and no result. -/

noncomputable section

namespace D5.S3.Observer.Separation.FiniteObservationRefinementBound

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift

/-- Equality of finite readout words through a fixed observation depth. -/
abbrev observationSetoid {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (m : Nat) : Setoid Y :=
  Setoid.ker (futureReadoutWord update readout m)

/-- A finite state carrier has finitely many finite-word observation classes. -/
noncomputable instance observationQuotientFintype {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    Fintype (PredictionState update readout m) :=
  by
    classical
    exact Fintype.ofSurjective (Quotient.mk _) Quotient.mk_surjective

/-- Number of equivalence classes visible through observation depth `m`. -/
def observationClassCount {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (m : Nat) : Nat :=
  Fintype.card (PredictionState update readout m)

/-- The least depth at which two consecutive observation relations agree. -/
def observationStabilityDepth {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) : Nat :=
  sInf {m | observationSetoid update readout m =
    observationSetoid update readout (m + 1)}

private theorem observation_setoid_succ_le {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    observationSetoid update readout (m + 1) <=
      observationSetoid update readout m := by
  intro y y' hword
  funext k
  exact congrFun hword k.castSucc

private theorem forget_latest_surjective {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    Function.Surjective (forgetLatest update readout m) := by
  intro state
  obtain ⟨y, rfl⟩ := Quotient.exists_rep state
  exact ⟨Quotient.mk _ y, rfl⟩

private theorem class_count_mono {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    observationClassCount update readout m <=
      observationClassCount update readout (m + 1) := by
  exact Fintype.card_le_of_surjective (forgetLatest update readout m)
    (forget_latest_surjective update readout m)

private theorem setoid_eq_of_class_count_eq {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hcount : observationClassCount update readout m =
      observationClassCount update readout (m + 1)) :
    observationSetoid update readout m =
      observationSetoid update readout (m + 1) := by
  have hbijective : Function.Bijective (forgetLatest update readout m) :=
    (Fintype.bijective_iff_surjective_and_card
      (forgetLatest update readout m)).2
      ⟨forget_latest_surjective update readout m, hcount.symm⟩
  apply Setoid.ext
  intro y y'
  constructor
  · intro hword
    apply Quotient.exact
    apply hbijective.1
    simpa only [forgetLatest, Quotient.map_mk, id_eq] using Quotient.sound hword
  · intro hword
    exact observation_setoid_succ_le update readout m hword

private theorem setoid_rel_iff_finite_relation {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) (y y' : Y) :
    (observationSetoid update readout m) y y' <->
      (y, y') ∈ finiteFutureRelation update readout m := by
  constructor
  · intro hword k hk
    simpa only [futureReadoutWord, observedAt] using
      congrFun hword (show Fin (m + 1) from ⟨k, Nat.lt_succ_of_le hk⟩)
  · intro hfuture
    funext k
    simpa only [futureReadoutWord, observedAt] using
      hfuture k (Nat.le_of_lt_succ k.isLt)

private theorem stable_relation_exists {Y O : Type*} [Finite Y]
    (update : Y -> Y) (readout : Y -> O) :
    exists m, observationSetoid update readout m =
      observationSetoid update readout (m + 1) := by
  letI := Fintype.ofFinite Y
  let m := stabilizationIndex update readout
  refine ⟨m, ?_⟩
  apply Setoid.ext
  intro y y'
  constructor
  · intro hword
    have hfinite : (y, y') ∈ finiteFutureRelation update readout m :=
      (setoid_rel_iff_finite_relation update readout m y y').mp hword
    have hinfinite : (y, y') ∈ infiniteFutureRelation update readout := by
      rw [infinite_relation_stabilizes update readout]
      exact hfinite
    apply (setoid_rel_iff_finite_relation update readout (m + 1) y y').mpr
    intro k _
    exact hinfinite k
  · intro hword
    exact observation_setoid_succ_le update readout m hword

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

private theorem class_count_le_state_count {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    observationClassCount update readout m <= Fintype.card Y := by
  exact Fintype.card_le_of_surjective (Quotient.mk _)
    Quotient.mk_surjective

/-- Finite future relations refine, their class counts increase, the least stable depth exists,
and every strict refinement before it consumes at least one available quotient class. -/
theorem finite_observation_refinement_and_stability_bound
    {Y O : Type*} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    (forall m, observationSetoid update readout (m + 1) <=
      observationSetoid update readout m) /\
    (forall m, observationClassCount update readout m <=
      observationClassCount update readout (m + 1)) /\
    ((observationSetoid update readout
        (observationStabilityDepth update readout) =
      observationSetoid update readout
        (observationStabilityDepth update readout + 1)) /\
      forall n, observationSetoid update readout n =
        observationSetoid update readout (n + 1) ->
        observationStabilityDepth update readout <= n) /\
    observationStabilityDepth update readout <=
      observationClassCount update readout
          (observationStabilityDepth update readout) -
        observationClassCount update readout 0 /\
    observationClassCount update readout
          (observationStabilityDepth update readout) -
        observationClassCount update readout 0 <=
      Fintype.card Y - Fintype.card O := by
  have hstableExists := stable_relation_exists update readout
  have hstable : observationSetoid update readout
      (observationStabilityDepth update readout) =
      observationSetoid update readout
        (observationStabilityDepth update readout + 1) := by
    exact Nat.sInf_mem hstableExists
  have hminimal : forall n, observationSetoid update readout n =
      observationSetoid update readout (n + 1) ->
      observationStabilityDepth update readout <= n := by
    intro n hn
    exact Nat.sInf_le hn
  have hgrowth : forall n, n <= observationStabilityDepth update readout ->
      observationClassCount update readout 0 + n <=
        observationClassCount update readout n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnlt : n < observationStabilityDepth update readout := by omega
        have hcountNe : observationClassCount update readout n ≠
            observationClassCount update readout (n + 1) := by
          intro hcount
          have hrelation := setoid_eq_of_class_count_eq update readout n hcount
          exact (Nat.not_le_of_lt hnlt) (hminimal n hrelation)
        have hstrict : observationClassCount update readout n <
            observationClassCount update readout (n + 1) :=
          lt_of_le_of_ne (class_count_mono update readout n) hcountNe
        have hprior := ih (by omega)
        omega
  have hcount0 := initial_class_count update readout hreadout
  have hupper := class_count_le_state_count update readout
    (observationStabilityDepth update readout)
  refine ⟨observation_setoid_succ_le update readout,
    class_count_mono update readout, ⟨hstable, hminimal⟩, ?_, ?_⟩
  · have h := hgrowth (observationStabilityDepth update readout) le_rfl
    omega
  · omega

/-- The finite-carrier assumption has a concrete inhabitant. -/
example : Fintype Unit := inferInstance

/-- The nonempty-carrier assumption has a concrete inhabitant. -/
example : Nonempty Unit := inferInstance

/-- The surjective-readout hypothesis is satisfiable on the concrete carrier. -/
example : Function.Surjective (id : Unit -> Unit) := Function.surjective_id

#print axioms finite_observation_refinement_and_stability_bound

end D5.S3.Observer.Separation.FiniteObservationRefinementBound
