/- GID: D5/S3/Observer/MemoryChronology/TimeOrderedMemoryChronologySignatureBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The time-ordered matrix logarithm recovers swap curvature and its Hopf reversal. -/

import D5.S3.Observer.AgencyHolonomy.TimeOrderedMemoryMatrixRepresentation
import D5.S3.Observer.Chronology.ChronologicalSignatureHopf
import Mathlib.Tactic

/-!
# Time-ordered memory as a chronological signature witness

The repository already has two exact chronology mechanisms:

* the time-ordered memory cocycle, represented by upper-triangular matrices;
* the generic step-two chronological signature, whose doubled logarithmic
  degree-two coordinate is a commutator.

This adapter identifies them on a two-event word. The upper-right entry of the
step-two Magnus coordinate is the negative of the frozen prime swap curvature.
Consequently every nonzero swap curvature is a concrete certificate that the
noncommutative step-two readout detects event order. The Hopf antipode is also
specialized to the timed matrix observation and realizes reverse-and-negate.

No continuous Magnus series, path-ordered exponential, infinite signature,
operator-domain theorem, zeta-zero statement, or physical arrow of time is
asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MemoryChronology.TimeOrderedMemoryChronologySignatureBridge

open D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
open D5.S3.Observer.AgencyHolonomy.PrimeSwapCurvature
open D5.S3.Observer.AgencyHolonomy.TimeOrderedMemoryMatrixRepresentation
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepTwoChronologicalLogarithm
open D5.S3.Observer.Chronology.ChronologicalSignatureHopf

noncomputable section

/-- The matrix algebra used by the frozen time-ordered memory transport. -/
abbrev TimedMemoryMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Observe one timed event by its exact upper-triangular transport matrix. -/
noncomputable def timedMatrixObservation (stable : ℂ) :
    TimedPrimeMemoryEvent → TimedMemoryMatrix :=
  timedEventMatrix stable

/-- For two timed events, the doubled degree-two logarithmic coordinate of the
matrix-valued chronological signature is their matrix commutator. -/
theorem timed_matrix_two_event_doubled_magnus_eq_commutator
    (stable : ℂ) (eventP eventQ : TimedPrimeMemoryEvent) :
    doubledMagnusDegreeTwo
        (chronologicalSignature (timedMatrixObservation stable)
          [eventP, eventQ]) =
      D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator
        (timedEventMatrix stable eventP)
        (timedEventMatrix stable eventQ) := by
  exact doubled_magnus_two_events_eq_commutator
    (timedMatrixObservation stable) eventP eventQ

/-- The upper-right entry of the matrix commutator is the negative of the
existing oriented memory swap curvature. The sign comes from the repository's
convention that the earlier event acts first, hence word matrices multiply in
reverse chronological order. -/
theorem timed_matrix_commutator_upper_right
    (stable : ℂ) (eventP eventQ : TimedPrimeMemoryEvent) :
    D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator
        (timedEventMatrix stable eventP)
        (timedEventMatrix stable eventQ) 0 1 =
      -primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor := by
  have hPQ :
      timeOrderedWordMatrix stable [eventP, eventQ] =
        timedEventMatrix stable eventQ *
          timedEventMatrix stable eventP := by
    calc
      timeOrderedWordMatrix stable [eventP, eventQ] =
          timeOrderedWordMatrix stable [eventQ] *
            timeOrderedWordMatrix stable [eventP] := by
        simpa using
          (time_ordered_word_matrix_append stable [eventP] [eventQ])
      _ = timedEventMatrix stable eventQ *
          timedEventMatrix stable eventP := by
        rw [time_ordered_word_matrix_singleton,
          time_ordered_word_matrix_singleton]
  have hQP :
      timeOrderedWordMatrix stable [eventQ, eventP] =
        timedEventMatrix stable eventP *
          timedEventMatrix stable eventQ := by
    calc
      timeOrderedWordMatrix stable [eventQ, eventP] =
          timeOrderedWordMatrix stable [eventP] *
            timeOrderedWordMatrix stable [eventQ] := by
        simpa using
          (time_ordered_word_matrix_append stable [eventQ] [eventP])
      _ = timedEventMatrix stable eventP *
          timedEventMatrix stable eventQ := by
        rw [time_ordered_word_matrix_singleton,
          time_ordered_word_matrix_singleton]
  have hSwap := two_event_matrix_swap_upper_right stable eventP eventQ
  rw [hPQ, hQP] at hSwap
  unfold D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator
  change
    (timedEventMatrix stable eventP * timedEventMatrix stable eventQ) 0 1 -
        (timedEventMatrix stable eventQ * timedEventMatrix stable eventP) 0 1 =
      -primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor
  linear_combination -hSwap

/-- The frozen swap curvature is exactly the oriented upper-right component of
the step-two chronological logarithm, up to the matrix-word sign convention. -/
theorem timed_matrix_two_event_doubled_magnus_upper_right
    (stable : ℂ) (eventP eventQ : TimedPrimeMemoryEvent) :
    (doubledMagnusDegreeTwo
        (chronologicalSignature (timedMatrixObservation stable)
          [eventP, eventQ])) 0 1 =
      -primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor := by
  rw [timed_matrix_two_event_doubled_magnus_eq_commutator,
    timed_matrix_commutator_upper_right]

/-- A nonzero memory swap curvature forces a nonzero step-two logarithmic
chronology witness. -/
theorem timed_matrix_two_event_order_detected
    (stable : ℂ) (eventP eventQ : TimedPrimeMemoryEvent)
    (hCurvature :
      primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor ≠ 0) :
    doubledMagnusDegreeTwo
        (chronologicalSignature (timedMatrixObservation stable)
          [eventP, eventQ]) ≠ 0 := by
  intro hZero
  have hEntry :
      (doubledMagnusDegreeTwo
          (chronologicalSignature (timedMatrixObservation stable)
            [eventP, eventQ])) 0 1 = 0 := by
    simpa using
      congrFun (congrFun hZero (0 : Fin 2)) (1 : Fin 2)
  rw [timed_matrix_two_event_doubled_magnus_upper_right] at hEntry
  exact hCurvature (neg_eq_zero.mp hEntry)

/-- Swapping the two timed events reverses the orientation of the complete
step-two logarithmic matrix coordinate. -/
theorem timed_matrix_two_event_doubled_magnus_swap
    (stable : ℂ) (eventP eventQ : TimedPrimeMemoryEvent) :
    doubledMagnusDegreeTwo
        (chronologicalSignature (timedMatrixObservation stable)
          [eventQ, eventP]) =
      -doubledMagnusDegreeTwo
        (chronologicalSignature (timedMatrixObservation stable)
          [eventP, eventQ]) := by
  exact doubled_magnus_two_events_swap
    (timedMatrixObservation stable) eventP eventQ

/-- On timed memory matrices, the finite Hopf antipode is realized by reversing
the event word and negating every event matrix. -/
theorem timed_matrix_signature_antipode_reverse_neg
    (stable : ℂ) (eventP eventQ : TimedPrimeMemoryEvent) :
    chronologicalSignature
        (fun event => -timedMatrixObservation stable event)
        [eventQ, eventP] =
      signatureAntipode
        (chronologicalSignature (timedMatrixObservation stable)
          [eventP, eventQ]) := by
  simpa [timedMatrixObservation] using
    (chronological_signature_reverse_neg
      (timedMatrixObservation stable) [eventP, eventQ])

#print axioms timed_matrix_two_event_doubled_magnus_eq_commutator
#print axioms timed_matrix_commutator_upper_right
#print axioms timed_matrix_two_event_doubled_magnus_upper_right
#print axioms timed_matrix_two_event_order_detected
#print axioms timed_matrix_two_event_doubled_magnus_swap
#print axioms timed_matrix_signature_antipode_reverse_neg

end

end D5.S3.Observer.MemoryChronology.TimeOrderedMemoryChronologySignatureBridge
