/- GID: D5/S3/Quantum/Dynamics/ConservationAutonomySeparation
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/ConservationAutonomySeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conservation and autonomous observable evolution are distinct. -/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.FiniteDimensional

/- Library-search audit trail (2026-08-25):
   * Exact family hit `hamiltonianPropagator` constructs the source Hamiltonian
     evolution and is imported rather than redeclared.
   * Exact family hits `qubitX`, `qubitZ`, and `qubit_weyl_star` supply the
     self-adjoint noncommuting witness.
   * Pinned Mathlib hits `SemiconjBy.exp_neg_mul_mul_exp_eq_self`,
     `Matrix.traceLinearMap`, and `Matrix.trace_mul_comm` are applied directly.
   * Repository and pinned-Mathlib searches found no theorem combining the
     conservation implication with an autonomous-but-nonstationary observable
     space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Dynamics.ConservationAutonomySeparation

open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.FiniteDimensional

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance (priority := 2000) : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAddCommGroup

local instance (priority := 2000) : NormedSpace ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedSpace

local instance (priority := 2000) : NormedRing (Matrix n n ℂ) :=
  Matrix.instL2OpNormedRing

local instance (priority := 2000) : NormedAlgebra ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAlgebra

local instance (priority := 2000) : NormedAlgebra ℚ (Matrix n n ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)

/-- A vanishing Hamiltonian commutator fixes an observable under Heisenberg
evolution. In contrast, the self-adjoint qubit `X` lies in the trace-zero
observable space, that whole space is invariant under commutation with the
self-adjoint qubit `Z`, and `X` itself has a nonzero commutator with `Z`. -/
theorem conservation_and_autonomy_are_distinct (H A : Matrix n n ℂ)
    (_hH : star H = H) (_hA : star A = A) :
    (H * A - A * H = 0 ->
      forall t : Real,
        hamiltonianPropagator H (-t) * A * hamiltonianPropagator H t = A) /\
    (star qubitZ = qubitZ /\
      star qubitX = qubitX /\
      qubitX ∈ LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ) /\
      (forall B : QubitMatrix,
        B ∈ LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ) ->
          qubitZ * B - B * qubitZ ∈
            LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)) /\
      qubitZ * qubitX - qubitX * qubitZ ≠ 0) := by
  constructor
  · intro hcommutator t
    have hcommute : Commute A H := by
      exact (sub_eq_zero.mp hcommutator).symm
    have hgenerator : Commute A (hamiltonianGenerator H) := by
      exact hcommute.smul_right (-Complex.I)
    have hscaled : Commute A (t • hamiltonianGenerator H) :=
      hgenerator.smul_right t
    have hexponential := hscaled.exp_neg_mul_mul_exp_eq_self
    simpa [hamiltonianPropagator] using hexponential
  · rcases qubit_weyl_star with
      ⟨_hanticommute, hXstar, hZstar, _hXsquare, _hZsquare⟩
    refine ⟨hZstar, hXstar, ?_, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      norm_num [Matrix.trace, qubitX]
    · intro B _hB
      rw [LinearMap.mem_ker]
      simp only [Matrix.traceLinearMap_apply, Matrix.trace_sub]
      exact sub_eq_zero.mpr (Matrix.trace_mul_comm qubitZ B)
    · intro hzero
      have hentry := congrFun (congrFun hzero (0 : Fin 2)) (1 : Fin 2)
      norm_num [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two] at hentry

example :
    forall t : Real,
      hamiltonianPropagator (0 : QubitMatrix) (-t) * qubitX *
          hamiltonianPropagator 0 t = qubitX := by
  exact (conservation_and_autonomy_are_distinct 0 qubitX (by simp)
    qubit_weyl_star.2.1).1 (by simp)

#print axioms conservation_and_autonomy_are_distinct

end D5.S3.Quantum.Dynamics.ConservationAutonomySeparation
