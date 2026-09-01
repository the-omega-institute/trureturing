/- GID: D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Time-ordered prime memory cocycles are exactly the upper-right entries of finite upper-triangular matrix transports. -/

import D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
import Mathlib.Tactic

/-!
# Matrix representation of time-ordered memory

Each timed memory event acts on `(memory, scalar)` by the upper-triangular
matrix

`[[stable, timedInjection], [0, localFactor]]`.

The matrix of a chronological word is multiplied in operational order. Its
upper-left entry is the stable power, its upper-right entry is exactly the
existing time-ordered memory cocycle, and its lower-right entry is exactly the
existing scalar cocycle. Matrix action therefore recovers the frozen affine
evolution without redefining it.

This file treats finite two-dimensional complex transport. It does not claim
continuous time ordering, a matrix exponential, Magnus convergence, or a
non-Abelian gauge theory.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.TimeOrderedMemoryMatrixRepresentation

open D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle

noncomputable section

/-- Column-vector encoding of a memory/scalar state. -/
def stateVector (state : ℂ × ℂ) : Fin 2 → ℂ :=
  ![state.1, state.2]

/-- Upper-triangular matrix of one timed memory event. -/
def timedEventMatrix
    (stable : ℂ) (event : TimedPrimeMemoryEvent) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![stable, timedInjection event; 0, event.localFactor]

/-- Matrix transport of a chronological word. The head event acts first. -/
def timeOrderedWordMatrix
    (stable : ℂ) :
    List TimedPrimeMemoryEvent → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | event :: laterWord =>
      timeOrderedWordMatrix stable laterWord *
        timedEventMatrix stable event

/-- One event matrix acts exactly as the existing affine update. -/
theorem timedEventMatrix_mulVec
    (stable : ℂ) (event : TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    (timedEventMatrix stable event).mulVec (stateVector state) =
      stateVector (timedPrimeUpdate stable event state) := by
  funext i
  fin_cases i <;>
    simp [timedEventMatrix, stateVector, timedPrimeUpdate,
      Matrix.mulVec, Fin.sum_univ_two]

/-- Concatenating chronological words reverses their matrix multiplication
order because column vectors are acted on from the left. -/
theorem timeOrderedWordMatrix_append
    (stable : ℂ)
    (earlierWord laterWord : List TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable (earlierWord ++ laterWord) =
      timeOrderedWordMatrix stable laterWord *
        timeOrderedWordMatrix stable earlierWord := by
  induction earlierWord with
  | nil =>
      simp [timeOrderedWordMatrix]
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, timeOrderedWordMatrix]
      rw [inductionHypothesis, Matrix.mul_assoc]

/-- The exact closed upper-triangular form of every finite chronological word. -/
theorem timeOrderedWordMatrix_closed_form
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable events =
      !![stable ^ events.length,
          timeOrderedMemoryCocycle stable events;
          0,
          timeOrderedScalarCocycle events] := by
  induction events with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [timeOrderedWordMatrix, timeOrderedMemoryCocycle,
          timeOrderedScalarCocycle, Matrix.one_apply]
  | cons event laterWord inductionHypothesis =>
      rw [timeOrderedWordMatrix, inductionHypothesis]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [timedEventMatrix, timeOrderedMemoryCocycle,
          timeOrderedScalarCocycle, Matrix.mul_apply,
          Fin.sum_univ_two, pow_succ] <;>
        ring

/-- The upper-right entry of the word matrix is the frozen memory cocycle. -/
theorem timeOrderedWordMatrix_upperRight
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable events 0 1 =
      timeOrderedMemoryCocycle stable events := by
  rw [timeOrderedWordMatrix_closed_form]
  rfl

/-- The diagonal entries are the stable transport power and scalar cocycle. -/
theorem timeOrderedWordMatrix_diagonal
    (stable : ℂ) (events : List TimedPrimeMemoryEvent) :
    timeOrderedWordMatrix stable events 0 0 =
        stable ^ events.length ∧
      timeOrderedWordMatrix stable events 1 1 =
        timeOrderedScalarCocycle events := by
  rw [timeOrderedWordMatrix_closed_form]
  exact ⟨rfl, rfl⟩

/-- Acting by the word matrix exactly recovers the frozen list evolution. -/
theorem timeOrderedWordMatrix_mulVec
    (stable : ℂ) (events : List TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    (timeOrderedWordMatrix stable events).mulVec (stateVector state) =
      stateVector (timeOrderedEvolution stable events state) := by
  rw [timeOrderedWordMatrix_closed_form,
    time_ordered_evolution_affine]
  funext i
  fin_cases i <;>
    simp [stateVector, Matrix.mulVec, Fin.sum_univ_two] <;>
    ring

/-- Equal word matrices have equal memory cocycles by reading the upper-right
entry. -/
theorem memoryCocycle_eq_of_wordMatrix_eq
    (stable : ℂ) {first second : List TimedPrimeMemoryEvent}
    (hMatrix : timeOrderedWordMatrix stable first =
      timeOrderedWordMatrix stable second) :
    timeOrderedMemoryCocycle stable first =
      timeOrderedMemoryCocycle stable second := by
  rw [← timeOrderedWordMatrix_upperRight stable first,
    ← timeOrderedWordMatrix_upperRight stable second, hMatrix]

example (stable : ℂ) :
    timeOrderedWordMatrix stable [] = 1 := by
  rfl

#print axioms timedEventMatrix_mulVec
#print axioms timeOrderedWordMatrix_append
#print axioms timeOrderedWordMatrix_closed_form
#print axioms timeOrderedWordMatrix_upperRight
#print axioms timeOrderedWordMatrix_mulVec
#print axioms memoryCocycle_eq_of_wordMatrix_eq

end

end D5.S3.Observer.AgencyHolonomy.TimeOrderedMemoryMatrixRepresentation
