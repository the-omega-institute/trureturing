/- GID: D5/S3/Quantum/Measurements/DeterministicReadoutCommutativity
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/DeterministicReadoutCommutativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Common-basis deterministic projections commute, while a qubit pair does not. -/

import D5.S3.Quantum.Measurements.DeterministicReadoutPvm
import D5.S3.Quantum.FiniteDimensional

noncomputable section

namespace D5.S3.Quantum.Measurements.DeterministicReadoutCommutativity

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Measurements.DeterministicReadoutPvm

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {X O I : Type*} [Fintype X]
  [DecidableEq X] [DecidableEq O]

theorem deterministic_readout_commutes_and_quantum_counterexample
    (readouts : I → X → O) :
    (∀ i j outcome outcome',
      deterministicProjection (readouts i) outcome *
          deterministicProjection (readouts j) outcome' =
        deterministicProjection (readouts j) outcome' *
          deterministicProjection (readouts i) outcome) ∧
      (∃ P Q : QubitMatrix,
        star P = P ∧ star Q = Q ∧ P * P = 1 ∧ Q * Q = 1 ∧
          P * Q ≠ Q * P) := by
  constructor
  · intro i j outcome outcome'
    simp only [deterministicProjection]
    exact (Matrix.commute_diagonal _ _).eq
  · rcases qubit_weyl_star with ⟨hAnti, hXStar, hZStar, hXSq, hZSq⟩
    have hNe : qubitZ * qubitX ≠ qubitX * qubitZ := by
      intro h
      have hentry := congrFun (congrFun h 0) 1
      norm_num [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two] at hentry
    have hNe' : qubitX * qubitZ ≠ qubitZ * qubitX := by
      intro h
      exact hNe h.symm
    exact ⟨qubitX, qubitZ, hXStar, hZStar, by simpa [pow_two] using hXSq,
      by simpa [pow_two] using hZSq, hNe'⟩

#print axioms deterministic_readout_commutes_and_quantum_counterexample

end D5.S3.Quantum.Measurements.DeterministicReadoutCommutativity
