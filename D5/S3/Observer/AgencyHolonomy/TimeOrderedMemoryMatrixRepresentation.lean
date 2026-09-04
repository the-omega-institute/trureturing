/- GID: D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen timed memory cocycle is the upper-right entry of a matrix word. -/

import D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
import Mathlib.Data.Matrix.Mul

/-!
# Matrix representation of the time-ordered memory cocycle

The existing timed prime memory update is affine in the memory/scalar state.
This module realizes it as multiplication by an upper-triangular two-by-two
complex matrix. A finite chronological event word is represented by the
reverse-ordered matrix product forced by the convention that the head event
acts first.

The summary matrix has entries

`[[stable ^ events.length, timeOrderedMemoryCocycle stable events],
  [0, timeOrderedScalarCocycle events]]`.

The existing affine evolution theorem and append cocycle laws are reused to
prove that this matrix acts exactly as `timeOrderedEvolution` and that word
concatenation is represented by matrix multiplication. The upper-right entry
of the two-event swap difference is the already frozen prime swap curvature.

No new memory recursion or curvature is introduced. This file does not claim
unitarity, matrix invertibility, continuous time evolution, a path-ordered
exponential, an infinite Magnus series, or RH.
-/

/- Library-search audit trail (2026-09-02):
   * `TimeOrderedPrimeMemoryCocycle` owns the event update, scalar cocycle,
     memory cocycle, affine evolution theorem, append laws, and two-event swap
     curvature. Every substantive identity below is transported from those
     frozen owners.
   * Pinned Mathlib's minimal `Matrix.Mul` module supplies matrix
     multiplication, `Matrix.mulVec`, `dotProduct`, and `Fin.sum_univ_two`.
     Ordinary functions replace the separate matrix-notation language, so the
     node does not enlarge the repository proof-language closure merely to
     write two-by-two literals.
   * `MemoryTransport` owns generic function-list composition but has no matrix
     representation or identification of the memory cocycle with a matrix
     entry.
   * Repository search found no owner of the upper-triangular matrix word
     representation formalized here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.TimeOrderedMemoryMatrixRepresentation

open D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
open D5.S3.Observer.AgencyHolonomy.PrimeSwapCurvature

noncomputable section

private def twoVector (first second : ℂ) : Fin 2 → ℂ :=
  fun index => if index = 0 then first else second

private def twoByTwoMatrix
    (upperLeft upperRight lowerLeft lowerRight : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun row column =>
    if row = 0 then
      if column = 0 then upperLeft else upperRight
    else if column = 0 then lowerLeft else lowerRight

/-- The state pair as a column vector in the same memory/scalar order. -/
def memoryStateVector (state : ℂ × ℂ) : Fin 2 → ℂ :=
  twoVector state.1 state.2

/-- One timed event as an upper-triangular memory transport matrix. -/
noncomputable def timedEventMatrix
    (stable : ℂ) (event : TimedPrimeMemoryEvent) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  twoByTwoMatrix stable (timedInjection event) 0 event.localFactor

/-- The exact matrix summary of a finite chronological word. -/
noncomputable def timeOrderedWordMatrix
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  twoByTwoMatrix
    (stable ^ events.length)
    (timeOrderedMemoryCocycle stable events)
    0
    (timeOrderedScalarCocycle events)

/-- Recursive matrix product in the chronology convention that the head event
acts first. -/
noncomputable def chronologicalMatrixProduct
    (stable : ℂ) : List TimedPrimeMemoryEvent →
      Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | event :: events =>
      chronologicalMatrixProduct stable events *
        timedEventMatrix stable event

/-- A single event matrix acts exactly as the frozen affine event update. -/
theorem timed_event_matrix_mulVec
    (stable : ℂ) (event : TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    Matrix.mulVec (timedEventMatrix stable event)
        (memoryStateVector state) =
      memoryStateVector (timedPrimeUpdate stable event state) := by
  funext index
  fin_cases index <;>
    simp [timedEventMatrix, memoryStateVector, twoVector, twoByTwoMatrix,
      timedPrimeUpdate, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The summary matrix acts exactly as the frozen list evolution. -/
theorem time_ordered_word_matrix_mulVec
    (stable : ℂ) (events : List TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    Matrix.mulVec (timeOrderedWordMatrix stable events)
        (memoryStateVector state) =
      memoryStateVector (timeOrderedEvolution stable events state) := by
  rw [time_ordered_evolution_affine]
  funext index
  fin_cases index <;>
    simp [timeOrderedWordMatrix, memoryStateVector, twoVector, twoByTwoMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- One-event word summaries are the corresponding event matrices. -/
theorem time_ordered_word_matrix_singleton
    (stable : ℂ) (event : TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable [event] =
      timedEventMatrix stable event := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [timeOrderedWordMatrix, timedEventMatrix, twoByTwoMatrix,
      timeOrderedMemoryCocycle, timeOrderedScalarCocycle]

/-- Concatenation of chronological words becomes reverse-ordered matrix
multiplication because the earlier word acts first. -/
theorem time_ordered_word_matrix_append
    (stable : ℂ)
    (earlierWord laterWord : List TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable (earlierWord ++ laterWord) =
      timeOrderedWordMatrix stable laterWord *
        timeOrderedWordMatrix stable earlierWord := by
  have cocycleLaws :=
    time_ordered_cocycle_append_laws stable earlierWord laterWord
  have scalarAppend := cocycleLaws.1
  have memoryAppend := cocycleLaws.2.1
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [timeOrderedWordMatrix, twoByTwoMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, List.length_append, pow_add,
      scalarAppend, memoryAppend]
  all_goals ring

/-- The recursive ordered matrix product equals the closed cocycle summary. -/
theorem chronological_matrix_product_eq_word_matrix
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    chronologicalMatrixProduct stable events =
      timeOrderedWordMatrix stable events := by
  induction events with
  | nil =>
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [chronologicalMatrixProduct, timeOrderedWordMatrix,
          twoByTwoMatrix, timeOrderedMemoryCocycle,
          timeOrderedScalarCocycle]
  | cons event events inductionHypothesis =>
      rw [chronologicalMatrixProduct, inductionHypothesis]
      simpa [time_ordered_word_matrix_singleton] using
        (time_ordered_word_matrix_append stable [event] events).symm

/-- The upper-right summary entry is exactly the frozen memory cocycle. -/
theorem time_ordered_word_matrix_upper_right
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable events 0 1 =
      timeOrderedMemoryCocycle stable events := by
  simp [timeOrderedWordMatrix, twoByTwoMatrix]

/-- The lower-right summary entry is exactly the frozen scalar cocycle. -/
theorem time_ordered_word_matrix_lower_right
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable events 1 1 =
      timeOrderedScalarCocycle events := by
  simp [timeOrderedWordMatrix, twoByTwoMatrix]

/-- The upper-right entry of the two-event chronology swap difference is the
already frozen prime swap curvature. -/
theorem two_event_matrix_swap_upper_right
    (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable [eventP, eventQ] 0 1 -
        timeOrderedWordMatrix stable [eventQ, eventP] 0 1 =
      primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor := by
  rw [time_ordered_word_matrix_upper_right,
    time_ordered_word_matrix_upper_right]
  exact
    (time_ordered_two_event_swap_curvature
      stable eventP eventQ (0, 1)).2.2

#print axioms timed_event_matrix_mulVec
#print axioms time_ordered_word_matrix_mulVec
#print axioms time_ordered_word_matrix_singleton
#print axioms time_ordered_word_matrix_append
#print axioms chronological_matrix_product_eq_word_matrix
#print axioms time_ordered_word_matrix_upper_right
#print axioms time_ordered_word_matrix_lower_right
#print axioms two_event_matrix_swap_upper_right

end

end D5.S3.Observer.AgencyHolonomy.TimeOrderedMemoryMatrixRepresentation
