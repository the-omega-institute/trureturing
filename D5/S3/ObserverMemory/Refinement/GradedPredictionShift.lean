/- GID: D5/S3/ObserverMemory/Refinement/GradedPredictionShift
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/GradedPredictionShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The graded shift closes on stabilized finite prediction quotients. -/

import D5.S3.ObserverMemory.Prediction.PredictionPartitionStability
import D5.S3.ObserverMemory.Refinement.PredictionCompletion

/- Library-search audit trail (2026-08-17):
   * Repository search found the exact permanent-stability theorem
     `prediction_partition_stable_forever` and the existing complete quotient
     and update; all are imported and applied below.
   * Exact pinned-Mathlib and Loogle hits `Quotient.map`,
     `Quotient.map_mk`, and `Quotient.map_surjective` supply the induced maps,
     representative equations, and surjectivity proof.
   * Exact pinned-Mathlib hits `Quotient.congr`, `Equiv.ofBijective`,
     `Quotient.mk_surjective`, and `Setoid.quotientKerEquivRange` supply the
     relation-change, stage, quotient-projection, and realized-word
     equivalences used below.
   * LeanSearch's shaped query endpoint returned HTTP 404 and no usable hit;
     repository and pinned-Mathlib searches found no theorem packaging the two
     maps, word deletion, stabilization bijection, and closed update together.
-/

namespace D5.S3.ObserverMemory.Refinement.GradedPredictionShift

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Prediction.PredictionPartitionStability
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- States identified by their readout words through a fixed depth. -/
abbrev PredictionState {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (m : Nat) :=
  Quotient (Setoid.ker (futureReadoutWord update readout m))

/-- The finite quotient is canonically equivalent to its realized words. -/
noncomputable def finiteWordRangeEquiv {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    PredictionState update readout m ≃
      Set.range (futureReadoutWord update readout m) :=
  Setoid.quotientKerEquivRange (futureReadoutWord update readout m)

/-- Delete the current coordinate of a word through depth `m + 1`. -/
def deleteCurrent {O : Type*} (m : Nat) (word : Fin (m + 2) -> O) :
    Fin (m + 1) -> O :=
  fun k => word ⟨k + 1, by omega⟩

/-- Update representatives while dropping the current readout coordinate. -/
private theorem graded_shift_respects {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    forall {y y'},
      (Setoid.ker (futureReadoutWord update readout (m + 1))) y y' ->
        (Setoid.ker (futureReadoutWord update readout m))
          (update y) (update y') := by
  intro y y' hword
  funext k
  have hcoordinate := congrFun hword
    (show Fin (m + 1 + 1) from ⟨k + 1, by omega⟩)
  simpa only [futureReadoutWord, Function.iterate_succ_apply] using hcoordinate

/-- Update representatives while dropping the current readout coordinate. -/
def gradedShift {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (m : Nat) :
    PredictionState update readout (m + 1) ->
      PredictionState update readout m :=
  @Quotient.map Y Y
    (Setoid.ker (futureReadoutWord update readout (m + 1)))
    (Setoid.ker (futureReadoutWord update readout m))
    update (by
      intro y y' hword
      exact graded_shift_respects update readout m hword)

/-- Forget the final coordinate of a finite readout word. -/
private theorem forget_latest_respects {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    forall {y y'},
      (Setoid.ker (futureReadoutWord update readout (m + 1))) y y' ->
        (Setoid.ker (futureReadoutWord update readout m)) (id y) (id y') := by
  intro y y' hword
  funext k
  have hcoordinate := congrFun hword
    (show Fin (m + 1 + 1) from ⟨k, by omega⟩)
  simpa only [futureReadoutWord, id_eq] using hcoordinate

/-- Forget the final coordinate of a finite readout word. -/
def forgetLatest {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (m : Nat) :
    PredictionState update readout (m + 1) ->
      PredictionState update readout m :=
  @Quotient.map Y Y
    (Setoid.ker (futureReadoutWord update readout (m + 1)))
    (Setoid.ker (futureReadoutWord update readout m))
    id (by
      intro y y' hword
      exact forget_latest_respects update readout m hword)

private theorem forget_latest_bijective {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout m) =
        Setoid.ker (futureReadoutWord update readout (m + 1))) :
    Function.Bijective (forgetLatest update readout m) := by
  constructor
  · intro first second heq
    obtain ⟨y, rfl⟩ := Quotient.exists_rep first
    obtain ⟨y', rfl⟩ := Quotient.exists_rep second
    apply Quotient.sound'
    rw [← hstable]
    simp only [forgetLatest, Quotient.map_mk] at heq
    exact Quotient.exact heq
  · change Function.Surjective
      (@Quotient.map Y Y
        (Setoid.ker (futureReadoutWord update readout (m + 1)))
        (Setoid.ker (futureReadoutWord update readout m))
        id (by
          intro y y' hword
          exact forget_latest_respects update readout m hword))
    exact Quotient.map_surjective
      (by
        intro y y' hword
        exact forget_latest_respects update readout m hword)
      Function.surjective_id

/-- Equality of consecutive relations identifies the two finite stages. -/
noncomputable def stageIdentification {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout m) =
        Setoid.ker (futureReadoutWord update readout (m + 1))) :
    PredictionState update readout (m + 1) ≃
      PredictionState update readout m :=
  Equiv.ofBijective (forgetLatest update readout m)
    (forget_latest_bijective update readout m hstable)

private theorem stable_relation_eq_complete {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout m) =
        Setoid.ker (futureReadoutWord update readout (m + 1))) :
    Setoid.ker (futureReadoutWord update readout m) =
      Setoid.ker (completeItinerary update readout) := by
  have hstep : forall y y',
      futureReadoutWord update readout m y =
          futureReadoutWord update readout m y' <->
        futureReadoutWord update readout (m + 1) y =
          futureReadoutWord update readout (m + 1) y' := by
    intro y y'
    exact Setoid.ext_iff.mp hstable y y'
  have hforever :=
    prediction_partition_stable_forever update readout m hstep
  apply Setoid.ext
  intro y y'
  change futureReadoutWord update readout m y =
      futureReadoutWord update readout m y' <->
    completeItinerary update readout y = completeItinerary update readout y'
  constructor
  · intro hword
    funext n
    have hlong := (hforever.2 n y y').mpr hword
    have hcoordinate := congrFun hlong
      (show Fin (m + n + 1) from ⟨n, by omega⟩)
    simpa only [futureReadoutWord, completeItinerary] using hcoordinate
  · intro hcomplete
    funext k
    simpa only [futureReadoutWord, completeItinerary] using congrFun hcomplete k

/-- At stabilization, the finite quotient is the complete prediction quotient. -/
def stableCompletionEquiv {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout m) =
        Setoid.ker (futureReadoutWord update readout (m + 1))) :
    PredictionState update readout m ≃ CompletedState update readout :=
  Quotient.congr (Equiv.refl Y) (by
    intro y y'
    change futureReadoutWord update readout m y =
        futureReadoutWord update readout m y' <->
      completeItinerary update readout y = completeItinerary update readout y'
    exact Setoid.ext_iff.mp
      (stable_relation_eq_complete update readout m hstable) y y')

/-- The update closes on a stabilized finite quotient. -/
def closedUpdate {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout m) =
        Setoid.ker (futureReadoutWord update readout (m + 1))) :
    PredictionState update readout m -> PredictionState update readout m :=
  Quotient.map update (by
    have hstep : forall y y',
        futureReadoutWord update readout m y =
            futureReadoutWord update readout m y' <->
          futureReadoutWord update readout (m + 1) y =
            futureReadoutWord update readout (m + 1) y' := by
      intro y y'
      exact Setoid.ext_iff.mp hstable y y'
    exact (prediction_partition_stable_forever update readout m hstep).1)

/-- The graded representative maps delete the appropriate finite-word
coordinate; after stabilization, the forgetful map is a bijection and the
shift becomes the closed update on the complete prediction quotient. -/
theorem graded_prediction_shift {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat) :
    (forall y,
      gradedShift update readout m
          (Quotient.mk _ y : PredictionState update readout (m + 1)) =
        (Quotient.mk _ (update y) : PredictionState update readout m)) /\
    (forall y,
      forgetLatest update readout m
          (Quotient.mk _ y : PredictionState update readout (m + 1)) =
        (Quotient.mk _ y : PredictionState update readout m)) /\
    (forall y,
      deleteCurrent m (futureReadoutWord update readout (m + 1) y) =
        futureReadoutWord update readout m (update y)) /\
    (forall y,
      restrictWord (Nat.le_succ m)
          (futureReadoutWord update readout (m + 1) y) =
        futureReadoutWord update readout m y) /\
    (forall hstable :
      Setoid.ker (futureReadoutWord update readout m) =
        Setoid.ker (futureReadoutWord update readout (m + 1)),
      Function.Bijective (forgetLatest update readout m) /\
        (forall y,
          stableCompletionEquiv update readout m hstable
              (Quotient.mk _ y : PredictionState update readout m) =
            completionProjection update readout y) /\
        (forall state,
          gradedShift update readout m state =
            closedUpdate update readout m hstable
              (stageIdentification update readout m hstable state)) /\
        (forall state,
          stableCompletionEquiv update readout m hstable
              (closedUpdate update readout m hstable state) =
            completionUpdate update readout
              (stableCompletionEquiv update readout m hstable state))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact Quotient.map_mk update
      (by
        intro a b hab
        exact graded_shift_respects update readout m hab) y
  · intro y
    exact Quotient.map_mk id
      (by
        intro a b hab
        exact forget_latest_respects update readout m hab) y
  · intro y
    funext k
    simp only [deleteCurrent, futureReadoutWord,
      Function.iterate_succ_apply]
  · intro y
    rfl
  · intro hstable
    refine ⟨forget_latest_bijective update readout m hstable, ?_, ?_, ?_⟩
    · intro y
      rfl
    · intro state
      refine Quotient.inductionOn' state fun y => ?_
      rfl
    · intro state
      refine Quotient.inductionOn' state fun y => ?_
      rfl

/- The quotient projection used above is independently surjective, including
on an inhabited nontrivial example. -/
example : Function.Surjective
    (Quotient.mk (Setoid.ker (futureReadoutWord Bool.not id 0))) :=
  Quotient.mk_surjective

example :
    Setoid.ker (futureReadoutWord Bool.not (fun _ => false) 0) =
      Setoid.ker (futureReadoutWord Bool.not (fun _ => false) (0 + 1)) := by
  apply Setoid.ext
  intro y y'
  constructor <;> intro _ <;> funext k <;> rfl

example : Nonempty (PredictionState Bool.not id 0) :=
  ⟨Quotient.mk _ false⟩

#print axioms graded_prediction_shift

end D5.S3.ObserverMemory.Refinement.GradedPredictionShift
