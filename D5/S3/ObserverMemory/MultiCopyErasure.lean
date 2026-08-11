/- GID: D5/S3/ObserverMemory/MultiCopyErasure
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/MultiCopyErasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize coherence loss across finitely many independent record copies. -/

/- Library-search audit trail (2026-08-12):
   * Local mathlib searches found `Finset.prod_map_toList`, `Finset.prod_eq_zero_iff`,
     and `Finset.prod_ne_zero_iff`, reused for the composition and finite-copy quantifiers.
   * The channel proof also reuses `mul_eq_zero` and `mul_ne_zero_iff`.
   * The record model, copied-address witness, and equal-superposition density are imported
     from the frozen record-overlap and measurement modules rather than redefined here. -/

import D5.S3.Observer.MeasurementMarginal

namespace D5.S3.ObserverMemory.MultiCopyErasure

open D5.S3.Observer.MeasurementMarginal
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses
open scoped BigOperators

/-- The product of the address overlaps for a finite family of independent records. -/
def multiRecordOverlap {Copy : Type*} [Fintype Copy]
    (records : Copy -> EnvironmentRecord) (i j : Fin 2) : ℂ :=
  ∏ k, recordOverlap (records k) i j

/-- Apply the frozen single-record channel once per member of a finite record family. -/
noncomputable def multiRecordChannel {Copy : Type*} [Fintype Copy]
    (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) : QubitMatrix :=
  Finset.univ.toList.foldr (fun k state => recordChannel (records k) state) rho

private theorem fold_record_channels_apply {Copy : Type*}
    (records : Copy -> EnvironmentRecord) (copies : List Copy)
    (rho : QubitMatrix) (i j : Fin 2) :
    (copies.foldr (fun k state => recordChannel (records k) state) rho) i j =
      (copies.map fun k => recordOverlap (records k) i j).prod * rho i j := by
  induction copies with
  | nil => simp
  | cons k copies ih => simp [recordChannel, ih, mul_assoc]

/-- Iterating the single-record channel multiplies each entry by all record overlaps. -/
theorem multi_record_channel_apply {Copy : Type*} [Fintype Copy]
    (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) (i j : Fin 2) :
    multiRecordChannel records rho i j = multiRecordOverlap records i j * rho i j := by
  simpa [multiRecordChannel, multiRecordOverlap] using
    fold_record_channels_apply records Finset.univ.toList rho i j

/--
At a nonzero input entry, the finite-copy channel erases that entry exactly when at least one
record copy has zero overlap there.
-/
theorem multi_copy_erasure_quantifier {Copy : Type*} [Fintype Copy]
    (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) (i j : Fin 2)
    (hRho : rho i j ≠ 0) :
    multiRecordChannel records rho i j = 0 ↔
      ∃ k, recordOverlap (records k) i j = 0 := by
  rw [multi_record_channel_apply]
  simp [multiRecordOverlap, hRho, Finset.prod_eq_zero_iff]

/--
Equivalently, a nonzero input entry survives exactly when every record copy has nonzero overlap.
-/
theorem multi_copy_erasure_nonzero_iff {Copy : Type*} [Fintype Copy]
    (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) (i j : Fin 2)
    (hRho : rho i j ≠ 0) :
    multiRecordChannel records rho i j ≠ 0 ↔
      ∀ k, recordOverlap (records k) i j ≠ 0 := by
  rw [multi_record_channel_apply]
  simp [multiRecordOverlap, hRho, Finset.prod_ne_zero_iff]

/-- A normalized record that carries no address distinction. -/
def addressIndependentRecord : EnvironmentRecord :=
  fun _ a => if a = 0 then 1 else 0

/--
Anti-vacuity certificate comparing two record families on the same original state. A family with
one copied-address record erases the selected entry. The counterfactual family with no
distinguishing record is evaluated separately on the original state and leaves that entry unchanged.
-/
theorem two_copy_erasure_certificate :
    let rho := equalSuperpositionDensity
    let distinguishingRecords : Fin 2 -> EnvironmentRecord := fun k =>
      if k = 0 then copiedAddressRecord else addressIndependentRecord
    let nonDistinguishingRecords : Fin 2 -> EnvironmentRecord :=
      fun _ => addressIndependentRecord
    rho 0 1 = 1 / 2 ∧
      recordOverlap (distinguishingRecords 0) 0 1 = 0 ∧
      recordOverlap (distinguishingRecords 1) 0 1 = 1 ∧
      multiRecordChannel distinguishingRecords rho 0 1 = 0 ∧
      multiRecordChannel nonDistinguishingRecords rho 0 1 = 1 / 2 := by
  simp [equalSuperpositionDensity, copiedAddressRecord, addressIndependentRecord,
    recordOverlap, multi_record_channel_apply, multiRecordOverlap]

end D5.S3.ObserverMemory.MultiCopyErasure
