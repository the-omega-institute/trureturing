/- GID: D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The time-ordered scalar and memory cocycles are exactly the diagonal and upper-right entries of a two-dimensional chronological matrix representation. -/

import D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Time-ordered memory matrix representation

Every timed memory event acts by an upper-triangular `2 × 2` complex matrix.
For a chronological event word `w`, the exact summary matrix is

`[[stable ^ length w, memoryCocycle w], [0, scalarCocycle w]]`.

Matrix-vector multiplication is exactly the previously frozen affine
`timeOrderedEvolution`. Concatenating an earlier word with a later word gives
the reverse matrix product `M(later) * M(earlier)`, matching the convention
that the head event acts first. For two events, the upper-right entry of the
matrix commutator is the frozen prime swap curvature.

This is a finite matrix representation theorem. It does not construct a
continuous connection, path-ordered exponential, infinite product, gauge
bundle, or analytic Magnus series.
-/

/- Library-search audit trail (2026-09-01):
   * `TimeOrderedPrimeMemoryCocycle` owns the affine evolution theorem and the
     exact scalar and memory append laws.
   * `MemoryTransport` owns only composition of arbitrary update functions and
     does not identify the cocycle with matrix entries.
   * Repository search found no existing `2 × 2` matrix owner for the timed
     memory cocycle.
   * Pinned Mathlib supplies finite matrix notation, matrix multiplication,
     matrix-vector multiplication, and `Fin 2` elimination. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix

namespace D5.S3.Observer.AgencyHolonomy.TimeOrderedMemoryMatrixRepresentation

open D5.S3.Observer.AgencyHolonomy.PrimeSwapCurvature
open D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle

noncomputable section

/-- Encode a pair as a column vector with two coordinates. -/
def stateVector (state : ℂ × ℂ) : Fin 2 → ℂ :=
  ![state.1, state.2]

/-- Matrix representing one timed memory event. -/
def timedEventMatrix
    (stable : ℂ) (event : TimedPrimeMemoryEvent) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![stable, timedInjection event;
     0, event.localFactor]

/-- Exact upper-triangular matrix summary of a chronological event word. -/
def memorySummaryMatrix
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![stable ^ events.length, timeOrderedMemoryCocycle stable events;
     0, timeOrderedScalarCocycle events]

/-- The summary matrix of one event is its local event matrix. -/
theorem memory_summary_matrix_singleton
    (stable : ℂ) (event : TimedPrimeMemoryEvent) :
    memorySummaryMatrix stable [event] = timedEventMatrix stable event := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [memorySummaryMatrix, timedEventMatrix,
      timeOrderedMemoryCocycle, timeOrderedScalarCocycle]

/-- Matrix-vector multiplication realizes the exact time-ordered affine
evolution. -/
theorem memory_summary_matrix_mulVec
    (stable : ℂ) (events : List TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    memorySummaryMatrix stable events *ᵥ stateVector state =
      stateVector (timeOrderedEvolution stable events state) := by
  rw [time_ordered_evolution_affine]
  funext i
  fin_cases i <;>
    simp [memorySummaryMatrix, stateVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- Chronological concatenation is represented by reverse matrix
multiplication because the earlier word acts first. -/
theorem memory_summary_matrix_append
    (stable : ℂ)
    (earlierWord laterWord : List TimedPrimeMemoryEvent) :
    memorySummaryMatrix stable (earlierWord ++ laterWord) =
      memorySummaryMatrix stable laterWord *
        memorySummaryMatrix stable earlierWord := by
  have hLaws :=
    time_ordered_cocycle_append_laws stable earlierWord laterWord
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [memorySummaryMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      List.length_append, pow_add, hLaws.1, hLaws.2.1] <;>
    ring

/-- The matrix representation sends append to sequential action on state
vectors. -/
theorem memory_summary_matrix_append_mulVec
    (stable : ℂ)
    (earlierWord laterWord : List TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    memorySummaryMatrix stable (earlierWord ++ laterWord) *ᵥ
        stateVector state =
      memorySummaryMatrix stable laterWord *ᵥ
        (memorySummaryMatrix stable earlierWord *ᵥ stateVector state) := by
  rw [memory_summary_matrix_append, Matrix.mulVec_mulVec]

/-- The upper-right summary entry is exactly the time-ordered memory cocycle. -/
theorem memory_summary_matrix_upper_right
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    memorySummaryMatrix stable events 0 1 =
      timeOrderedMemoryCocycle stable events := by
  rfl

/-- The lower-right summary entry is exactly the scalar cocycle. -/
theorem memory_summary_matrix_lower_right
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    memorySummaryMatrix stable events 1 1 =
      timeOrderedScalarCocycle events := by
  rfl

/-- The upper-left summary entry records the accumulated stable transport. -/
theorem memory_summary_matrix_upper_left
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    memorySummaryMatrix stable events 0 0 =
      stable ^ events.length := by
  rfl

/-- The upper-right entry of the two-event matrix commutator is exactly the
prime swap curvature. -/
theorem timed_event_matrix_commutator_upper_right
    (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent) :
    (timedEventMatrix stable eventQ * timedEventMatrix stable eventP -
        timedEventMatrix stable eventP * timedEventMatrix stable eventQ) 0 1 =
      primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor := by
  simp [timedEventMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    primeSwapCurvature]
  ring

/-- Swapping two events changes the upper-right summary entry by the existing
prime swap curvature. -/
theorem memory_summary_matrix_two_event_swap
    (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent) :
    memorySummaryMatrix stable [eventP, eventQ] 0 1 -
        memorySummaryMatrix stable [eventQ, eventP] 0 1 =
      primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor := by
  simpa [memorySummaryMatrix] using
    (time_ordered_two_event_swap_curvature
      stable eventP eventQ (0, 1)).2.2

example :
    memorySummaryMatrix 1 [] =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [memorySummaryMatrix, timeOrderedMemoryCocycle,
      timeOrderedScalarCocycle, Matrix.one_apply]

#print axioms memory_summary_matrix_singleton
#print axioms memory_summary_matrix_mulVec
#print axioms memory_summary_matrix_append
#print axioms memory_summary_matrix_append_mulVec
#print axioms timed_event_matrix_commutator_upper_right
#print axioms memory_summary_matrix_two_event_swap

end

end D5.S3.Observer.AgencyHolonomy.TimeOrderedMemoryMatrixRepresentation
