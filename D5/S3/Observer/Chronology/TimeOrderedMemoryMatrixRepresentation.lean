/- GID: D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation
   generality: I
   mirror-B: D5/B/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Time-ordered affine memory evolution is exactly an upper-triangular matrix representation of chronological words. -/

import D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Matrix representation of the time-ordered memory cocycle

Each timed memory event acts on the column state `(memory, scalar)` through the
upper-triangular matrix

`[[stable, timedInjection event], [0, event.localFactor]]`.

Because the head event acts first, the matrix of a chronological list is the
reverse ordered product.  The resulting matrix has diagonal entries
`stable ^ length` and the scalar cocycle, while its upper-right entry is
exactly the time-ordered memory cocycle.  Matrix multiplication therefore
realizes the append law and the complete affine evolution.

This file is a finite two-dimensional representation theorem.  It does not
construct a continuous connection, a path-ordered exponential, an infinite
Magnus series, or differential-geometric holonomy.
-/

/- Library-search audit trail (2026-09-01):
   * `TimeOrderedPrimeMemoryCocycle` owns timed events, effective injections,
     affine updates, scalar and memory cocycles, and list evolution.
   * `MemoryTransport` owns only composition of arbitrary update functions and
     does not provide a matrix representation.
   * Repository search found no existing matrix whose upper-right entry is the
     frozen time-ordered memory cocycle.
   * Pinned Mathlib supplies finite matrix notation, `mulVec`, and explicit
     sums over `Fin 2`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Observer.Chronology.TimeOrderedMemoryMatrixRepresentation

open D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle

noncomputable section

/-- Column-vector encoding of a memory/scalar state. -/
def pairVector (state : ℂ × ℂ) : Fin 2 → ℂ :=
  ![state.1, state.2]

/-- Decode a two-component column vector as memory and scalar coordinates. -/
def vectorPair (vector : Fin 2 → ℂ) : ℂ × ℂ :=
  (vector 0, vector 1)

/-- Upper-triangular matrix of one timed memory event. -/
def timedPrimeUpdateMatrix
    (stable : ℂ) (event : TimedPrimeMemoryEvent) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![stable, timedInjection event;
     0, event.localFactor]

/-- One-event matrix action is exactly the frozen affine update. -/
theorem timed_prime_update_matrix_mulVec
    (stable : ℂ) (event : TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    vectorPair
        ((timedPrimeUpdateMatrix stable event).mulVec (pairVector state)) =
      timedPrimeUpdate stable event state := by
  apply Prod.ext <;>
    simp [vectorPair, pairVector, timedPrimeUpdateMatrix,
      timedPrimeUpdate, Matrix.mulVec, Fin.sum_univ_two]

/-- Reverse ordered matrix product of a chronological event list. -/
def timeOrderedMemoryMatrix
    (stable : ℂ) : List TimedPrimeMemoryEvent →
      Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | event :: events =>
      timeOrderedMemoryMatrix stable events *
        timedPrimeUpdateMatrix stable event

/-- Concatenating chronological words becomes reversed matrix multiplication,
because the earlier word acts first on column states. -/
theorem time_ordered_memory_matrix_append
    (stable : ℂ)
    (earlierWord laterWord : List TimedPrimeMemoryEvent) :
    timeOrderedMemoryMatrix stable (earlierWord ++ laterWord) =
      timeOrderedMemoryMatrix stable laterWord *
        timeOrderedMemoryMatrix stable earlierWord := by
  induction earlierWord with
  | nil =>
      simp [timeOrderedMemoryMatrix]
  | cons event earlierWord inductionHypothesis =>
      simp only [List.cons_append, timeOrderedMemoryMatrix,
        inductionHypothesis]
      rw [Matrix.mul_assoc]

/-- The chronological matrix has the exact triangular cocycle form. -/
theorem time_ordered_memory_matrix_entries
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedMemoryMatrix stable events =
      !![stable ^ events.length,
          timeOrderedMemoryCocycle stable events;
         0, timeOrderedScalarCocycle events] := by
  induction events with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [timeOrderedMemoryMatrix, timeOrderedMemoryCocycle,
          timeOrderedScalarCocycle, Matrix.one_apply]
  | cons event events inductionHypothesis =>
      rw [timeOrderedMemoryMatrix, inductionHypothesis]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [timedPrimeUpdateMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          timeOrderedMemoryCocycle, timeOrderedScalarCocycle, pow_succ] <;>
        ring

/-- The upper-right matrix entry is exactly the time-ordered memory cocycle. -/
theorem time_ordered_memory_matrix_zero_one
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedMemoryMatrix stable events 0 1 =
      timeOrderedMemoryCocycle stable events := by
  rw [time_ordered_memory_matrix_entries]
  rfl

/-- The lower-right matrix entry is exactly the scalar cocycle. -/
theorem time_ordered_memory_matrix_one_one
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedMemoryMatrix stable events 1 1 =
      timeOrderedScalarCocycle events := by
  rw [time_ordered_memory_matrix_entries]
  rfl

/-- The upper-left matrix entry records the stable transport depth. -/
theorem time_ordered_memory_matrix_zero_zero
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedMemoryMatrix stable events 0 0 =
      stable ^ events.length := by
  rw [time_ordered_memory_matrix_entries]
  rfl

/-- The matrix representation acts exactly as the complete chronological
affine evolution. -/
theorem time_ordered_memory_matrix_mulVec
    (stable : ℂ) (events : List TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    vectorPair
        ((timeOrderedMemoryMatrix stable events).mulVec (pairVector state)) =
      timeOrderedEvolution stable events state := by
  rw [time_ordered_evolution_affine,
    time_ordered_memory_matrix_entries]
  apply Prod.ext <;>
    simp [vectorPair, pairVector, Matrix.mulVec, Fin.sum_univ_two] <;>
    ring

example (stable : ℂ) :
    timeOrderedMemoryMatrix stable [] = 1 := by
  rfl

#print axioms timed_prime_update_matrix_mulVec
#print axioms time_ordered_memory_matrix_append
#print axioms time_ordered_memory_matrix_entries
#print axioms time_ordered_memory_matrix_zero_one
#print axioms time_ordered_memory_matrix_mulVec

end

end D5.S3.Observer.Chronology.TimeOrderedMemoryMatrixRepresentation
