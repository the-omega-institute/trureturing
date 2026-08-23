/- GID: D5/S3/Observer/Prediction/CanonicalSignatureCompletion
   generality: G
   mirror-B: D5/B/S3/Observer/Prediction/CanonicalSignatureCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical signatures recover finite words, the canonical stable depth, and completion. -/

import D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization
import D5.S3.Observer.Separation.FiniteObservationRefinementBound

/- Library-search audit trail (2026-08-23):
   * Repository exact hits `Signature`, `controlledSignature`, and
     `controlled_signature_algorithm_correctness` supply the canonical signature family and its
     controlled-word correctness theorem; they are imported and applied below.
   * Repository exact hits `observationStabilityDepth` and
     `finite_observation_refinement_and_stability_bound` supply the canonical adjacent-partition
     stopping depth and its leastness; no new depth or stability predicate is declared.
   * Repository exact hits `stableCompletionEquiv`, `CompletedState`, and
     `completionProjection`, together with pinned-Mathlib's
     `Setoid.quotientKerEquivRange` and `Quotient.congr`, construct the final canonical
     equivalence. No exact singleton-input bridge to finite future words was found. -/

noncomputable section

namespace D5.S3.Observer.Prediction.CanonicalSignatureCompletion

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.ObserverMemory.Algorithms.ControlledSignatureStabilization
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

private theorem run_word_singleton_update
    {Y : Type*} (update : Y -> Y) (word : List PUnit) (y : Y) :
    runWord (fun _ : PUnit => update) word y = (update^[word.length]) y := by
  induction word generalizing y with
  | nil => rfl
  | cons input word ih =>
      simpa [runWord, Function.iterate_succ_apply] using ih (update y)

private theorem canonical_signature_matches_finite_future
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) (y y' : Y) :
    controlledSignature (fun _ : PUnit => update) readout depth y =
        controlledSignature (fun _ : PUnit => update) readout depth y' <->
      (y, y') ∈ finiteFutureRelation update readout depth := by
  letI : Nonempty O := ⟨readout (Classical.choice inferInstance)⟩
  rw [(controlled_signature_algorithm_correctness
    (fun _ : PUnit => update) readout hreadout).1 depth y y']
  constructor
  · intro hbounded k hk
    have hword := hbounded (List.replicate k PUnit.unit) (by simpa using hk)
    simpa [run_word_singleton_update, observedAt] using hword
  · intro hfuture word hlength
    simpa [run_word_singleton_update, observedAt] using
      hfuture word.length hlength

private theorem canonical_signature_matches_future_word
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) (y y' : Y) :
    controlledSignature (fun _ : PUnit => update) readout depth y =
        controlledSignature (fun _ : PUnit => update) readout depth y' <->
      futureReadoutWord update readout depth y =
        futureReadoutWord update readout depth y' := by
  rw [canonical_signature_matches_finite_future update readout hreadout depth y y']
  constructor
  · intro hfuture
    funext k
    simpa only [futureReadoutWord, observedAt] using
      hfuture k (Nat.le_of_lt_succ k.isLt)
  · intro hword k hk
    simpa only [futureReadoutWord, observedAt] using
      congrFun hword (show Fin (depth + 1) from ⟨k, Nat.lt_succ_of_le hk⟩)

private theorem canonical_signature_kernel_matches_observation
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) :
    Setoid.ker
        (controlledSignature (fun _ : PUnit => update) readout depth) =
      observationSetoid update readout depth := by
  apply Setoid.ext
  intro y y'
  exact canonical_signature_matches_future_word
    update readout hreadout depth y y'

private theorem observation_stable_at_canonical_depth
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    Setoid.ker
        (futureReadoutWord update readout
          (observationStabilityDepth update readout)) =
      Setoid.ker
        (futureReadoutWord update readout
          (observationStabilityDepth update readout + 1)) := by
  exact
    (finite_observation_refinement_and_stability_bound
      update readout hreadout).2.2.1.1

private def canonicalSignatureRangePredictionEquiv
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) :
    Set.range (controlledSignature (fun _ : PUnit => update) readout depth) ≃
      PredictionState update readout depth :=
  (Setoid.quotientKerEquivRange
      (controlledSignature (fun _ : PUnit => update) readout depth)).symm |>.trans
    (Quotient.congr (Equiv.refl Y)
      (canonical_signature_matches_future_word
        update readout hreadout depth))

private theorem canonical_signature_range_prediction_equiv_apply
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (depth : Nat) (y : Y) :
    canonicalSignatureRangePredictionEquiv update readout hreadout depth
        ⟨controlledSignature (fun _ : PUnit => update) readout depth y,
          ⟨y, rfl⟩⟩ =
      (Quotient.mk _ y : PredictionState update readout depth) := by
  change
    Quotient.congr (Equiv.refl Y)
        (canonical_signature_matches_future_word
          update readout hreadout depth)
        ((Setoid.quotientKerEquivRange
          (controlledSignature (fun _ : PUnit => update) readout depth)).symm
          ⟨controlledSignature (fun _ : PUnit => update) readout depth y,
            ⟨y, rfl⟩⟩) =
      Quotient.mk _ y
  have hrange :
      (Setoid.quotientKerEquivRange
          (controlledSignature (fun _ : PUnit => update) readout depth)).symm
          ⟨controlledSignature (fun _ : PUnit => update) readout depth y,
            ⟨y, rfl⟩⟩ =
        Quotient.mk _ y := by
    apply (Setoid.quotientKerEquivRange
      (controlledSignature (fun _ : PUnit => update) readout depth)).injective
    simp only [Equiv.apply_symm_apply]
    rfl
  rw [hrange]
  rfl

/-- The canonical equivalence from realized canonical signatures at the existing observation
stability depth to the existing complete-future quotient. -/
def canonicalFinalSignatureCompletionEquiv
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    Set.range
        (controlledSignature (fun _ : PUnit => update) readout
          (observationStabilityDepth update readout)) ≃
      CompletedState update readout :=
  (canonicalSignatureRangePredictionEquiv update readout hreadout
      (observationStabilityDepth update readout)).trans
    (stableCompletionEquiv update readout
      (observationStabilityDepth update readout)
      (observation_stable_at_canonical_depth update readout hreadout))

private theorem canonical_final_signature_completion_equiv_apply
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) (y : Y) :
    canonicalFinalSignatureCompletionEquiv update readout hreadout
        ⟨controlledSignature (fun _ : PUnit => update) readout
            (observationStabilityDepth update readout) y,
          ⟨y, rfl⟩⟩ =
      completionProjection update readout y := by
  change
    stableCompletionEquiv update readout
        (observationStabilityDepth update readout)
        (observation_stable_at_canonical_depth update readout hreadout)
        (canonicalSignatureRangePredictionEquiv update readout hreadout
          (observationStabilityDepth update readout)
          ⟨controlledSignature (fun _ : PUnit => update) readout
              (observationStabilityDepth update readout) y,
            ⟨y, rfl⟩⟩) =
      completionProjection update readout y
  rw [canonical_signature_range_prediction_equiv_apply]
  rfl

/-- Canonical recursive signatures equal the finite-future-word partition at every depth. Their
first repeated adjacent partition occurs exactly at the canonical observation stability depth,
and the named final equivalence sends every realized signature label to its existing complete
prediction class. -/
theorem canonical_signature_labels_stable_depth_and_completion
    {Y O : Type u} [Fintype Y] [Fintype O] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    (forall depth y y',
      controlledSignature (fun _ : PUnit => update) readout depth y =
          controlledSignature (fun _ : PUnit => update) readout depth y' <->
        (y, y') ∈ finiteFutureRelation update readout depth) /\
    ((Setoid.ker
          (controlledSignature (fun _ : PUnit => update) readout
            (observationStabilityDepth update readout)) =
        Setoid.ker
          (controlledSignature (fun _ : PUnit => update) readout
            (observationStabilityDepth update readout + 1))) /\
      (forall depth,
        Setoid.ker
            (controlledSignature (fun _ : PUnit => update) readout depth) =
          Setoid.ker
            (controlledSignature (fun _ : PUnit => update) readout (depth + 1)) ->
        observationStabilityDepth update readout <= depth)) /\
    (let finalEquiv :=
        canonicalFinalSignatureCompletionEquiv update readout hreadout
      forall y,
        finalEquiv
            ⟨controlledSignature (fun _ : PUnit => update) readout
                (observationStabilityDepth update readout) y,
              ⟨y, rfl⟩⟩ =
          completionProjection update readout y) := by
  have observationResult :=
    finite_observation_refinement_and_stability_bound update readout hreadout
  refine ⟨canonical_signature_matches_finite_future update readout hreadout,
    ⟨?_, ?_⟩, ?_⟩
  · calc
      Setoid.ker
          (controlledSignature (fun _ : PUnit => update) readout
            (observationStabilityDepth update readout)) =
          observationSetoid update readout
            (observationStabilityDepth update readout) :=
        canonical_signature_kernel_matches_observation update readout hreadout _
      _ = observationSetoid update readout
            (observationStabilityDepth update readout + 1) :=
        observationResult.2.2.1.1
      _ = Setoid.ker
          (controlledSignature (fun _ : PUnit => update) readout
            (observationStabilityDepth update readout + 1)) :=
        (canonical_signature_kernel_matches_observation
          update readout hreadout _).symm
  · intro depth hstable
    apply observationResult.2.2.1.2 depth
    calc
      observationSetoid update readout depth =
          Setoid.ker
            (controlledSignature (fun _ : PUnit => update) readout depth) :=
        (canonical_signature_kernel_matches_observation
          update readout hreadout depth).symm
      _ = Setoid.ker
            (controlledSignature (fun _ : PUnit => update) readout (depth + 1)) :=
        hstable
      _ = observationSetoid update readout (depth + 1) :=
        canonical_signature_kernel_matches_observation
          update readout hreadout (depth + 1)
  · dsimp only
    exact canonical_final_signature_completion_equiv_apply update readout hreadout

#print axioms canonical_signature_labels_stable_depth_and_completion

end D5.S3.Observer.Prediction.CanonicalSignatureCompletion
