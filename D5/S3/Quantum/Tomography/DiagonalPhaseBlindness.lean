/- GID: D5/S3/Quantum/Tomography/DiagonalPhaseBlindness
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/DiagonalPhaseBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Diagonal families cannot recover relative phase without a non-diagonal interface. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.Quantum.QubitWitnesses

/- Library-search audit trail (2026-08-26):
   * Exact repository hits `jointReadout`, `bornProbability`,
     `equalSuperpositionDensity`, `qubitZ`, and `qubitX` supply the canonical
     family readout, trace expectation, and one shared phase countermodel.
   * Repository searches for diagonal-family phase blindness, relative-phase
     recovery, and a non-diagonal distinguishing interface found no theorem
     containing both public clauses. The existing projective probability-fiber
     theorem proves torus-shaped fibers but does not expose the interface clause.
   * Pinned Mathlib provides the exact predicate `Matrix.IsDiag`; searches for
     an expectation or trace-separation theorem specialized to diagonal
     matrices found no exact result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Tomography.DiagonalPhaseBlindness

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

/-- Every indexed family of diagonal qubit observables has the same joint
expectations on the equal superposition and its relative-phase flip. Any
observable that distinguishes this same pair must be non-diagonal, and the
canonical `X` interface does distinguish it. -/
theorem diagonal_prime_observables_cannot_recover_relative_phase
    {I : Type*} :
    (forall observable : I -> QubitMatrix,
      (forall i, (observable i).IsDiag) ->
        equalSuperpositionDensity ≠
            qubitZ * equalSuperpositionDensity * qubitZ /\
          jointReadout (fun i rho => bornProbability rho (observable i))
              equalSuperpositionDensity =
            jointReadout (fun i rho => bornProbability rho (observable i))
              (qubitZ * equalSuperpositionDensity * qubitZ)) /\
    (forall interface : QubitMatrix,
      bornProbability equalSuperpositionDensity interface ≠
          bornProbability (qubitZ * equalSuperpositionDensity * qubitZ) interface ->
        Not interface.IsDiag) /\
    (Not qubitX.IsDiag /\
      bornProbability equalSuperpositionDensity qubitX ≠
        bornProbability (qubitZ * equalSuperpositionDensity * qubitZ) qubitX) := by
  have phase_states_distinct :
      equalSuperpositionDensity ≠
        qubitZ * equalSuperpositionDensity * qubitZ := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    norm_num [equalSuperpositionDensity, qubitZ, Matrix.mul_apply,
      Fin.sum_univ_two] at h01
  have diagonal_expectation_equal (observable : QubitMatrix)
      (hDiagonal : observable.IsDiag) :
      bornProbability equalSuperpositionDensity observable =
        bornProbability (qubitZ * equalSuperpositionDensity * qubitZ) observable := by
    have h01 : observable 0 1 = 0 := hDiagonal (by decide)
    have h10 : observable 1 0 = 0 := hDiagonal (by decide)
    simp [bornProbability, equalSuperpositionDensity, qubitZ, Matrix.trace,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, h01, h10]
  constructor
  · intro observable hDiagonal
    refine ⟨phase_states_distinct, ?_⟩
    funext i
    exact diagonal_expectation_equal (observable i) (hDiagonal i)
  constructor
  · intro interface hDistinguishes hDiagonal
    exact hDistinguishes (diagonal_expectation_equal interface hDiagonal)
  · constructor
    · intro hDiagonal
      have h01 : qubitX 0 1 = 0 := hDiagonal (by decide)
      norm_num [qubitX] at h01
    · norm_num [bornProbability, equalSuperpositionDensity, qubitX, qubitZ,
        Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

#print axioms diagonal_prime_observables_cannot_recover_relative_phase

end D5.S3.Quantum.Tomography.DiagonalPhaseBlindness
