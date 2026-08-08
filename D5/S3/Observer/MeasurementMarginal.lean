/- GID: D5/S3/Observer/MeasurementMarginal
   generality: G
   mirror-B: D5/B/S3/Observer/MeasurementMarginal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quantify coherence loss while any copied address record survives. -/

import D5.S3.Quantum.EnvironmentRecords

namespace D5.S3.Observer.MeasurementMarginal

open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open scoped BigOperators

/- Library-search audit trail (2026-08-08):
   * Local mathlib and D5 searches for `partialTrace`, `partial trace`, `environment marginal`,
     `unread state`, `pinching`, `Lueders`, and projective measurement found no theorem for this
     concrete copied-record marginal or its partially erased indexed-copy form.
   * The proof reuses `Finset.sum_mul` and `Finset.prod_eq_zero` from mathlib, plus the joint-state,
     environment-trace, overlap, and channel definitions from `EnvironmentRecords`.
   Interface deviation: `Conditioning` is absent from this worktree's `origin/dev`. This module
   therefore states the concrete address-block sum directly; it does not redeclare
   `Conditioning.IsRecordMeasurement` or `Conditioning.unreadState`. Once `Conditioning` lands,
   a downstream bridge may identify this sum with its canonical unread state.
   Ownership note: the generic controlled-record trace identity lives in `EnvironmentRecords`;
   only the concrete copied-address consequences remain here.
-/

variable {copyIndex : Type*} [Fintype copyIndex] [DecidableEq copyIndex]

/-- The standard projector onto one address of the two-point system. -/
def addressProjection (k : Fin 2) : QubitMatrix :=
  fun i j => if i = k ∧ j = k then 1 else 0

/-- The environment vector that copies each system address into the matching basis record. -/
def copiedAddressRecord : EnvironmentRecord :=
  fun i a => if i = a then 1 else 0

/-- One copied address record leaves exactly the sum of the two diagonal address blocks. -/
theorem copied_record_partial_trace_eq_address_blocks (rho : QubitMatrix) :
    traceEnvironment (controlledRecordJointState copiedAddressRecord rho) =
      ∑ k, addressProjection k * rho * addressProjection k := by
  rw [trace_environment_controlled_record_eq_record_channel]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordChannel, recordOverlap, copiedAddressRecord,
      addressProjection, Matrix.mul_apply, Fin.sum_univ_two]

/-- The marginal after erasing indexed independent environment copies.
Each retained copy contributes its Gram overlap; an erased index contributes no factor. -/
def retainedCopiesMarginal (records : copyIndex -> EnvironmentRecord) (erased : Finset copyIndex)
    (rho : QubitMatrix) : QubitMatrix :=
  fun i j =>
    (∏ k ∈ Finset.univ \ erased, recordOverlap (records k) i j) * rho i j

/-- If any indexed address copy survives erasure, no off-diagonal entry is restored. -/
theorem surviving_copied_record_offDiagonal_eq_zero
    (records : copyIndex -> EnvironmentRecord) (erased : Finset copyIndex)
    (rho : QubitMatrix) (i j : Fin 2) (hij : i ≠ j)
    (hSurvives : ∃ k, k ∉ erased ∧ records k = copiedAddressRecord) :
    retainedCopiesMarginal records erased rho i j = 0 := by
  obtain ⟨k, hkErased, hkRecord⟩ := hSurvives
  have hkRetained : k ∈ Finset.univ \ erased := by simp [hkErased]
  have hkZero : recordOverlap (records k) i j = 0 := by
    rw [hkRecord]
    fin_cases i <;> fin_cases j <;>
      simp_all [recordOverlap, copiedAddressRecord]
  rw [retainedCopiesMarginal, Finset.prod_eq_zero hkRetained hkZero, zero_mul]

end D5.S3.Observer.MeasurementMarginal
