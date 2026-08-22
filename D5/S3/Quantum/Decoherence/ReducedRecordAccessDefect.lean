/- GID: D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/ReducedRecordAccessDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reversible record coupling can hide coherence from every reduced-state decoder. -/

/- Library-search audit trail (2026-08-22):
   * Repository search found the canonical environment-record state and partial-trace operations
     in `EnvironmentRecords`, and the canonical unitary evolution in
     `ProjectedUnistochasticDynamics`; all are imported and used directly below.
   * Pinned-Mathlib and Loogle exact-name searches found `Matrix.mem_unitaryGroup_iff`, while
     local search also found `Matrix.conjTranspose_permMatrix`, `Matrix.permMatrix_mul`,
     `PEquiv.toMatrix_toPEquiv_mul`, and `PEquiv.mul_toMatrix_toPEquiv`; each applicable hit is
     used directly.
   * The LeanSearch executable was unavailable and its former API endpoint returned HTTP 404.
     Repository and pinned-Mathlib searches found no theorem combining reversible record
     generation, coincident reduced states, joint-state separation, and recovery obstruction.
-/

import D5.S3.Quantum.EnvironmentRecords
import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import Mathlib.LinearAlgebra.Matrix.Permutation

noncomputable section

namespace D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect

open Matrix
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The controlled copy of a system bit into a two-component environment. -/
def copyPermutation : Equiv.Perm (Fin 2 × Fin 2) where
  toFun p := if p.1 = 0 then p else (p.1, 1 - p.2)
  invFun p := if p.1 = 0 then p else (p.1, 1 - p.2)
  left_inv := by
    rintro ⟨i, a⟩
    fin_cases i <;> fin_cases a <;> decide
  right_inv := by
    rintro ⟨i, a⟩
    fin_cases i <;> fin_cases a <;> decide

/-- The permutation matrix of the controlled environment copy. -/
def copyUnitary : JointQubitEnvironmentMatrix :=
  copyPermutation.permMatrix ℂ

/-- Put a system matrix next to the blank environment record. -/
def blankEnvironmentJointState (rho : QubitMatrix) : JointQubitEnvironmentMatrix :=
  fun ia jb => if ia.2 = 0 ∧ jb.2 = 0 then rho ia.1 jb.1 else 0

/-- The orthogonal record written by copying each system address. -/
def copiedAddressRecord : EnvironmentRecord :=
  fun i a => if a = i then 1 else 0

private theorem copy_permutation_involutive : copyPermutation⁻¹ = copyPermutation := by
  apply Equiv.ext
  rintro ⟨i, a⟩
  fin_cases i <;> fin_cases a <;> rfl

private theorem copy_unitary_is_unitary :
    copyUnitary ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [copyUnitary, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp

private theorem copy_evolution_reindexes (rho : JointQubitEnvironmentMatrix) :
    unitaryEvolution copyUnitary rho =
      rho.submatrix copyPermutation copyPermutation := by
  rw [unitaryEvolution, copyUnitary, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, copy_permutation_involutive,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  rfl

private theorem copy_evolution_writes_record (rho : QubitMatrix) :
    unitaryEvolution copyUnitary (blankEnvironmentJointState rho) =
      controlledRecordJointState copiedAddressRecord rho := by
  rw [copy_evolution_reindexes]
  ext ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    simp [copyPermutation, blankEnvironmentJointState, controlledRecordJointState,
      copiedAddressRecord]

private theorem trace_copied_record (rho : QubitMatrix) :
    traceEnvironment (controlledRecordJointState copiedAddressRecord rho) =
      fun i j => if i = j then rho i j else 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceEnvironment, controlledRecordJointState, copiedAddressRecord]

private theorem copied_record_injective {rho sigma : QubitMatrix}
    (hne : rho ≠ sigma) :
    controlledRecordJointState copiedAddressRecord rho ≠
      controlledRecordJointState copiedAddressRecord sigma := by
  intro heq
  apply hne
  ext i j
  have hentry := congrFun (congrFun heq (i, i)) (j, j)
  simpa [controlledRecordJointState, copiedAddressRecord] using hentry

private theorem inverse_copy_evolution_recovers (rho : QubitMatrix) :
    unitaryEvolution (star copyUnitary)
        (controlledRecordJointState copiedAddressRecord rho) =
      blankEnvironmentJointState rho := by
  rw [← copy_evolution_writes_record]
  unfold unitaryEvolution
  have hleft : star copyUnitary * copyUnitary = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp copy_unitary_is_unitary
  simp only [star_star]
  calc
    star copyUnitary *
          (copyUnitary * blankEnvironmentJointState rho * star copyUnitary) *
        copyUnitary =
        (star copyUnitary * copyUnitary) * blankEnvironmentJointState rho *
          (star copyUnitary * copyUnitary) := by noncomm_ring
    _ = blankEnvironmentJointState rho := by rw [hleft]; simp

/-- A reversible controlled record coupling preserves distinct coherence in distinct joint
states, although tracing the record identifies their reduced states. Consequently no function
of the reduced state alone can recover both joint records, while coherent control of the record
and the adjoint global coupling restores both blank-record inputs exactly. -/
theorem reduced_irreversibility_is_access_defect
    (rho sigma : QubitMatrix)
    (hdiag : ∀ i, rho i i = sigma i i)
    (hcoherence : ∃ i j, i ≠ j ∧ rho i j ≠ sigma i j) :
    copyUnitary ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ ∧
      (unitaryEvolution copyUnitary (blankEnvironmentJointState rho) =
          controlledRecordJointState copiedAddressRecord rho ∧
        unitaryEvolution copyUnitary (blankEnvironmentJointState sigma) =
          controlledRecordJointState copiedAddressRecord sigma) ∧
      traceEnvironment (controlledRecordJointState copiedAddressRecord rho) =
        traceEnvironment (controlledRecordJointState copiedAddressRecord sigma) ∧
      controlledRecordJointState copiedAddressRecord rho ≠
        controlledRecordJointState copiedAddressRecord sigma ∧
      (¬ ∃ recover : QubitMatrix → JointQubitEnvironmentMatrix,
        recover (traceEnvironment (controlledRecordJointState copiedAddressRecord rho)) =
            controlledRecordJointState copiedAddressRecord rho ∧
          recover (traceEnvironment (controlledRecordJointState copiedAddressRecord sigma)) =
            controlledRecordJointState copiedAddressRecord sigma) ∧
      (unitaryEvolution (star copyUnitary)
            (controlledRecordJointState copiedAddressRecord rho) =
          blankEnvironmentJointState rho ∧
        unitaryEvolution (star copyUnitary)
            (controlledRecordJointState copiedAddressRecord sigma) =
          blankEnvironmentJointState sigma) := by
  have hne : rho ≠ sigma := by
    rintro rfl
    obtain ⟨i, j, _, hij⟩ := hcoherence
    exact hij rfl
  have htrace :
      traceEnvironment (controlledRecordJointState copiedAddressRecord rho) =
        traceEnvironment (controlledRecordJointState copiedAddressRecord sigma) := by
    rw [trace_copied_record, trace_copied_record]
    funext i j
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp [hij]
  have hjoint := copied_record_injective hne
  refine ⟨copy_unitary_is_unitary, ⟨copy_evolution_writes_record rho,
    copy_evolution_writes_record sigma⟩, htrace, hjoint, ?_,
    ⟨inverse_copy_evolution_recovers rho, inverse_copy_evolution_recovers sigma⟩⟩
  rintro ⟨recover, hrho, hsigma⟩
  apply hjoint
  rw [← hrho, ← hsigma, htrace]

example :
    ∃ rho sigma : QubitMatrix,
      (∀ i, rho i i = sigma i i) ∧
        ∃ i j, i ≠ j ∧ rho i j ≠ sigma i j := by
  let rho : QubitMatrix := !![(1 : ℂ) / 2, (1 : ℂ) / 2; (1 : ℂ) / 2, (1 : ℂ) / 2]
  let sigma : QubitMatrix := !![(1 : ℂ) / 2, -(1 : ℂ) / 2; -(1 : ℂ) / 2, (1 : ℂ) / 2]
  refine ⟨rho, sigma, ?_, 0, 1, by decide, ?_⟩
  · intro i
    fin_cases i <;> simp [rho, sigma]
  · norm_num [rho, sigma]

#print axioms reduced_irreversibility_is_access_defect

end D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect
