/- GID: D5/S3/Observer/MeasurementMarginal
   generality: G
   mirror-B: D5/B/S3/Observer/MeasurementMarginal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive copied-address decoherence from a traced joint state. -/

import D5.S3.Quantum.EnvironmentRecords

namespace D5.S3.Observer.MeasurementMarginal

open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open scoped BigOperators

/- Library-search audit trail (2026-08-08):
   * Local mathlib and D5 searches for `partialTrace`, `partial trace`, `environment marginal`,
     `unread state`, `pinching`, `Lueders`, and projective measurement found no theorem identifying
     this concrete copied-record marginal with an unread measurement map.
   * The proof reuses `Finset.sum_mul` from mathlib, plus the joint-state, environment-trace,
     overlap, and channel definitions from `EnvironmentRecords`.
   Interface deviation: `Conditioning` is absent from this worktree's `origin/dev`. This module
   therefore states the concrete address-block sum directly; it does not redeclare
   `Conditioning.IsRecordMeasurement` or `Conditioning.unreadState`. Once `Conditioning` lands,
   a downstream bridge may identify this sum with its canonical unread state.
   Ownership note: the generic controlled-record trace identity lives in `EnvironmentRecords`;
   only the concrete copied-address consequences remain here.
   Unresolved: a multiple-environment statement requires a joint state over all copy factors,
   a subsystem partial trace, and an explicit erasure operation. Those generic quantum
   constructions are deferred to an environment-infrastructure round rather than postulated here.
-/

/-- The standard projector onto one address of the two-point system. -/
def addressProjection (k : Fin 2) : QubitMatrix :=
  fun i j => if i = k ∧ j = k then 1 else 0

/-- The environment vector that copies each system address into the matching basis record. -/
def copiedAddressRecord : EnvironmentRecord :=
  fun i a => if i = a then 1 else 0

/-- Tracing the environment of any controlled record gives its record channel.
    Local bridge only: the natural home is the frozen `EnvironmentRecords` module,
    which cannot gain statements without a Reattest event; kept `private` here so it
    is not a second public truth source. -/
private theorem trace_environment_controlled_record_eq_record_channel
    (record : EnvironmentRecord) (rho : QubitMatrix) :
    traceEnvironment (controlledRecordJointState record rho) = recordChannel record rho := by
  ext i j
  change (∑ a, record i a * star (record j a) * rho i j) =
    recordOverlap record i j * rho i j
  rw [← Finset.sum_mul]
  rfl

/-- One copied address record leaves exactly the sum of the two diagonal address blocks. -/
theorem copied_record_partial_trace_eq_address_blocks (rho : QubitMatrix) :
    traceEnvironment (controlledRecordJointState copiedAddressRecord rho) =
      ∑ k, addressProjection k * rho * addressProjection k := by
  rw [trace_environment_controlled_record_eq_record_channel]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordChannel, recordOverlap, copiedAddressRecord,
      addressProjection, Matrix.mul_apply, Fin.sum_univ_two]

/-- The traced joint state of one copied address record has no off-diagonal system entry. -/
theorem copied_record_partial_trace_offDiagonal_eq_zero
    (rho : QubitMatrix) (i j : Fin 2) (hij : i ≠ j) :
    traceEnvironment (controlledRecordJointState copiedAddressRecord rho) i j = 0 := by
  rw [copied_record_partial_trace_eq_address_blocks]
  fin_cases i <;> fin_cases j <;>
    simp_all [addressProjection, Matrix.mul_apply, Fin.sum_univ_two]

end D5.S3.Observer.MeasurementMarginal
