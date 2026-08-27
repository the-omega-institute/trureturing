/- GID: D5/S3/Quantum/Measurement/WordProbabilityTraceRepresentation
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/WordProbabilityTraceRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Operational instrument-word probabilities equal Schrödinger and Heisenberg traces. -/

import D5.S3.Quantum.Completion.SequentialWordObservationResidual
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.Fibers.OperatorSystemTowerStability

/- Library-search audit trail (2026-08-27):
   * Exact family hit `SequentialWordObservationResidual.sequentialWordEffect`
     is the canonical source-order Heisenberg fold and is reused directly.
   * Exact family hits `MatrixAlgebra`, `heisenbergOnHermitian`, and
     `DensityState` provide the finite matrix, Hermitian-effect, and state
     carriers without redeclaration.
   * Body-shape searches for a Schrödinger instrument fold and recursively
     evaluated word probability found no D5 primitive. The operational
     probability below follows the source recursion on branch substates.
   * Repository and pinned-Mathlib searches found no exact theorem packaging
     both trace equalities. List recursion and the supplied trace-duality law
     give the two proof steps. -/

open scoped CStarAlgebra ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation

open D5.S3.Quantum.Completion.SequentialWordObservationResidual
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Fibers.OperatorSystemTowerStability

/-- The probability of a remaining instrument word, evaluated recursively on
the current subnormalized branch state. -/
noncomputable def operationalWordProbability
    {d : Nat} {Alphabet : Type*}
    (instrument : Alphabet -> MatrixAlgebra (Fin d) →CP MatrixAlgebra (Fin d))
    (state : MatrixAlgebra (Fin d)) : List Alphabet -> ℂ
  | [] => Matrix.trace state
  | generator :: rest =>
      operationalWordProbability instrument (instrument generator state) rest

private theorem operational_probability_eq_trace_foldl
    {d : Nat} {Alphabet : Type*}
    (instrument : Alphabet -> MatrixAlgebra (Fin d) →CP MatrixAlgebra (Fin d))
    (state : MatrixAlgebra (Fin d)) (word : List Alphabet) :
    operationalWordProbability instrument state word =
      Matrix.trace
        (word.foldl (fun current generator => instrument generator current) state) := by
  induction word generalizing state with
  | nil => rfl
  | cons generator rest ih =>
      change operationalWordProbability instrument (instrument generator state) rest =
        Matrix.trace
          (rest.foldl (fun current next => instrument next current)
            (instrument generator state))
      exact ih (instrument generator state)

private theorem trace_foldl_eq_word_effect
    {d : Nat} {Alphabet : Type*}
    (instrument instrumentDual :
      Alphabet -> MatrixAlgebra (Fin d) →CP MatrixAlgebra (Fin d))
    (hduality : forall generator state effect,
      Matrix.trace (instrument generator state * effect) =
        Matrix.trace (state * instrumentDual generator effect))
    (state : MatrixAlgebra (Fin d)) (word : List Alphabet) :
    Matrix.trace
        (word.foldl (fun current generator => instrument generator current) state) =
      Matrix.trace
        (state *
          CStarMatrix.ofMatrix
            (sequentialWordEffect
              (fun generator => heisenbergOnHermitian (instrumentDual generator)) word).1) := by
  induction word generalizing state with
  | nil =>
      change Matrix.trace state =
        Matrix.trace (state * (1 : MatrixAlgebra (Fin d)))
      rw [mul_one]
  | cons generator rest ih =>
      calc
        Matrix.trace
            ((generator :: rest).foldl
              (fun current next => instrument next current) state) =
          Matrix.trace
            (rest.foldl (fun current next => instrument next current)
              (instrument generator state)) := rfl
        _ = Matrix.trace
            (instrument generator state *
              CStarMatrix.ofMatrix
                (sequentialWordEffect
                  (fun next => heisenbergOnHermitian (instrumentDual next)) rest).1) :=
          ih (instrument generator state)
        _ = Matrix.trace
            (state * instrumentDual generator
              (CStarMatrix.ofMatrix
                (sequentialWordEffect
                  (fun next => heisenbergOnHermitian (instrumentDual next)) rest).1)) :=
          hduality generator state _
        _ = Matrix.trace
            (state *
              CStarMatrix.ofMatrix
                (sequentialWordEffect
                (fun next => heisenbergOnHermitian (instrumentDual next))
                (generator :: rest)).1) := rfl

/-- The recursively evaluated operational probability of a finite branch word
equals the trace of its Schrödinger branch composite, and that trace equals the
initial-state pairing with the canonical Heisenberg word effect. -/
theorem word_probability_trace_representation
    {d : Nat} {Alphabet : Type*}
    (instrument instrumentDual :
      Alphabet -> MatrixAlgebra (Fin d) →CP MatrixAlgebra (Fin d))
    (hduality : forall generator state effect,
      Matrix.trace (instrument generator state * effect) =
        Matrix.trace (state * instrumentDual generator effect))
    (rho : DensityState (Fin d)) (word : List Alphabet) :
    operationalWordProbability instrument rho.1 word =
        Matrix.trace
          (word.foldl (fun current generator => instrument generator current) rho.1) /\
      Matrix.trace
          (word.foldl (fun current generator => instrument generator current) rho.1) =
        Matrix.trace
          (rho.1 *
            CStarMatrix.ofMatrix
              (sequentialWordEffect
                (fun generator => heisenbergOnHermitian (instrumentDual generator)) word).1) := by
  exact
    ⟨operational_probability_eq_trace_foldl instrument rho.1 word,
      trace_foldl_eq_word_effect instrument instrumentDual hduality rho.1 word⟩

#print axioms word_probability_trace_representation

end D5.S3.Quantum.Measurement.WordProbabilityTraceRepresentation
