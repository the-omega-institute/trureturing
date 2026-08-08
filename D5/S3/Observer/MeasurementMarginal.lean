/- GID: D5/S3/Observer/MeasurementMarginal
   generality: G
   mirror-B: D5/B/S3/Observer/MeasurementMarginal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify copied-record marginals with unread measurement states. -/

import D5.S3.Quantum.EnvironmentRecords

namespace D5.S3.Observer.MeasurementMarginal

open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open scoped BigOperators

/- Library-search audit trail (2026-08-08):
   * Local mathlib and D5 searches for `partialTrace`, `partial trace`, `environment marginal`,
     `unread state`, `pinching`, and `Lueders` found no theorem identifying this concrete
     controlled-record marginal with an unread measurement map.
   * The generic marginal calculation reuses `Finset.sum_mul` from mathlib and the joint-state,
     environment-trace, overlap, and channel definitions from `EnvironmentRecords`.
   Deviation: `Conditioning` is not present on the `origin/dev` base used by this worktree.
   The next two declarations reproduce only its `IsRecordMeasurement` and `unreadState`
   interfaces, with identical signatures. After that module lands, this file must import it and
   remove these local copies; no compatibility alias is intended.
-/

variable {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa] [DecidableEq kappa]
    {P : kappa -> Matrix n n ℂ}

/-- A finite complete family of pairwise orthogonal self-adjoint projections.
Temporary local interface matching `Conditioning.IsRecordMeasurement`. -/
structure IsRecordMeasurement (P : kappa -> Matrix n n ℂ) : Prop where
  selfAdjoint : forall k, star (P k) = P k
  idempotent : forall k, P k * P k = P k
  orthogonal : forall k l, k ≠ l -> P k * P l = 0
  complete : ∑ k, P k = 1

/-- The state obtained by measuring the record and then discarding its value.
Temporary local interface matching `Conditioning.unreadState`. -/
def unreadState (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, P k * rho * P k

/-- The standard projector onto one address of the two-point system. -/
def addressProjection (k : Fin 2) : QubitMatrix :=
  fun i j => if i = k ∧ j = k then 1 else 0

/-- The standard address projections form a record measurement. -/
theorem addressProjection_isRecordMeasurement : IsRecordMeasurement addressProjection := by
  constructor
  · intro k
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [addressProjection]
  · intro k
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [addressProjection, Matrix.mul_apply]
  · intro k l hkl
    ext i j
    fin_cases k <;> fin_cases l <;> fin_cases i <;> fin_cases j <;>
      simp_all [addressProjection, Matrix.mul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [addressProjection, Fin.sum_univ_two]

/-- The environment vector that copies each system address into the matching basis record. -/
def copiedAddressRecord : EnvironmentRecord :=
  fun i a => if i = a then 1 else 0

/-- Tracing the environment of any controlled record gives its record channel. -/
theorem trace_environment_controlled_record_eq_record_channel
    (record : EnvironmentRecord) (rho : QubitMatrix) :
    traceEnvironment (controlledRecordJointState record rho) = recordChannel record rho := by
  ext i j
  change (∑ a, record i a * star (record j a) * rho i j) =
    recordOverlap record i j * rho i j
  rw [← Finset.sum_mul]
  rfl

/-- The system marginal left by one copied address record is the corresponding unread state. -/
theorem copied_record_partial_trace_eq_unread (rho : QubitMatrix) :
    traceEnvironment (controlledRecordJointState copiedAddressRecord rho) =
      unreadState addressProjection rho := by
  rw [trace_environment_controlled_record_eq_record_channel]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordChannel, recordOverlap, copiedAddressRecord, unreadState,
      addressProjection, Matrix.mul_apply, Fin.sum_univ_two]

/-- A surviving orthogonal address copy leaves every off-diagonal system entry zero. -/
theorem copied_record_partial_trace_offDiagonal_eq_zero
    (rho : QubitMatrix) (i j : Fin 2) (hij : i != j) :
    traceEnvironment (controlledRecordJointState copiedAddressRecord rho) i j = 0 :=
  by
    fin_cases i <;> fin_cases j <;>
      simp_all [traceEnvironment, controlledRecordJointState, copiedAddressRecord]

end D5.S3.Observer.MeasurementMarginal
