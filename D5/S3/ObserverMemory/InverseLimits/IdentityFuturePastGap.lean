/- GID: D5/S3/ObserverMemory/InverseLimits/IdentityFuturePastGap
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/IdentityFuturePastGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identity readout preserves every finite state while infinite pasts retain only periodic states. -/

import D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion
import Mathlib.Data.Fintype.EquivFin

/- Library-search audit trail (2026-08-18):
   * The repository theorem `backward_orbit_eval_zero_bijective` is an exact
     hit for the inverse-limit/periodic-core equivalence and is applied below.
   * The repository definition `completeItinerary` and Mathlib's exact theorem
     `Setoid.quotientKerEquivRange` construct the future relation and its
     quotient completion; both are reused below.
   * Pinned Mathlib supplies `Function.injective_iff_periodicPts_eq_univ`,
     `Fintype.card_lt_of_injective_not_surjective`, and `Nat.card_congr`.
   * Repository and pinned-Mathlib searches found no theorem combining the
     identity relation, both equivalences, and the strict cardinality gap.
     Neither Loogle nor LeanSearch was installed in the worker environment. -/

namespace D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap

open D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/-- Two states are future-indistinguishable when every iterated readout agrees. -/
def FutureIndistinguishable {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (y y' : Y) : Prop :=
  completeItinerary tau q y = completeItinerary tau q y'

/-- The predictive completion obtained by quotienting states with identical
complete future readouts. -/
abbrev PredictionCompletion {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :=
  Quotient (Setoid.ker (completeItinerary tau q))

/-- The positive-period points of a self-map. -/
abbrev PeriodicCore {Y : Type*} (tau : Y -> Y) :=
  {y : Y // y ∈ Function.periodicPts tau}

/-- Reading coordinate zero identifies every realized identity-readout
itinerary with its initial state. -/
def identityItineraryEvalZero {Y : Type*} (tau : Y -> Y) :
    ItineraryRange tau (fun y : Y => y) -> Y :=
  fun itinerary => itinerary.1 0

private theorem identity_itinerary_eval_zero_bijective
    {Y : Type*} (tau : Y -> Y) :
    Function.Bijective (identityItineraryEvalZero tau) := by
  constructor
  · rintro ⟨_, ⟨y, rfl⟩⟩ ⟨_, ⟨y', rfl⟩⟩ h
    apply Subtype.ext
    funext n
    change (tau^[n]) y = (tau^[n]) y'
    change y = y' at h
    rw [h]
  · intro y
    refine ⟨⟨completeItinerary tau (fun z : Y => z) y, ⟨y, rfl⟩⟩, ?_⟩
    simp [identityItineraryEvalZero, completeItinerary]

/-- The canonical equivalence from the identity-readout completion to the
original state space. -/
noncomputable def identityCompletionEquiv {Y : Type*} (tau : Y -> Y) :
    PredictionCompletion tau (fun y : Y => y) ≃ Y :=
  (Setoid.quotientKerEquivRange
    (completeItinerary tau (fun y : Y => y))).trans
      (Equiv.ofBijective (identityItineraryEvalZero tau)
        (identity_itinerary_eval_zero_bijective tau))

/-- The canonical coordinate-zero equivalence from infinite backward orbits
to the periodic core. -/
noncomputable def pastCoreEquiv {Y : Type*} [Finite Y] (tau : Y -> Y) :
    BackwardOrbit tau ≃ PeriodicCore tau :=
  Equiv.ofBijective
    (fun orbit : BackwardOrbit tau =>
      (⟨orbit.1 0, backward_orbit_coordinate_periodic orbit 0⟩ :
        PeriodicCore tau))
    (backward_orbit_eval_zero_bijective tau)

private theorem periodic_core_card_lt
    {Y : Type*} [Fintype Y] (tau : Y -> Y)
    (hNotPermutation : ¬Function.Bijective tau) :
    Nat.card (PeriodicCore tau) < Nat.card Y := by
  classical
  have hNotInjective : ¬Function.Injective tau := by
    intro hInjective
    exact hNotPermutation
      ⟨hInjective, Finite.injective_iff_surjective.mp hInjective⟩
  have hCard : Fintype.card (PeriodicCore tau) < Fintype.card Y := by
    apply Fintype.card_lt_of_injective_not_surjective
      (fun point : PeriodicCore tau => point.1) Subtype.val_injective
    intro hSurjective
    apply hNotInjective
    rw [Function.injective_iff_periodicPts_eq_univ]
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨point, hpoint⟩ := hSurjective y
    rw [<- hpoint]
    exact point.2
  simpa [Nat.card_eq_fintype_card] using hCard

/-- Identity readout separates all states, whereas a non-permutation finite
self-map has fewer compatible infinite pasts because only periodic states can
occur in them. -/
theorem identity_future_completion_exceeds_past_core
    {Y : Type*} [Fintype Y] (tau : Y -> Y)
    (hNotPermutation : ¬Function.Bijective tau) :
    (forall y y' : Y,
      FutureIndistinguishable tau (fun z : Y => z) y y' <-> y = y') /\
      Nonempty (PredictionCompletion tau (fun z : Y => z) ≃ Y) /\
      Nonempty (BackwardOrbit tau ≃ PeriodicCore tau) /\
      Nat.card (PeriodicCore tau) < Nat.card Y /\
      Nat.card (BackwardOrbit tau) <
        Nat.card (PredictionCompletion tau (fun z : Y => z)) := by
  have hRelation : forall y y' : Y,
      FutureIndistinguishable tau (fun z : Y => z) y y' <-> y = y' := by
    intro y y'
    constructor
    · intro h
      have hzero := congrFun h 0
      simpa [FutureIndistinguishable, completeItinerary] using hzero
    · intro h
      subst y'
      rfl
  have hCore := periodic_core_card_lt tau hNotPermutation
  refine ⟨hRelation, ⟨identityCompletionEquiv tau⟩,
    ⟨pastCoreEquiv tau⟩, hCore, ?_⟩
  calc
    Nat.card (BackwardOrbit tau) = Nat.card (PeriodicCore tau) :=
      Nat.card_congr (pastCoreEquiv tau)
    _ < Nat.card Y := hCore
    _ = Nat.card (PredictionCompletion tau (fun z : Y => z)) :=
      (Nat.card_congr (identityCompletionEquiv tau)).symm

#print axioms identity_future_completion_exceeds_past_core

end D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
