/- GID: D5/S3/ObserverMemory/JointCoherentReversal
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/JointCoherentReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Undo finite record-channel phase factors by conjugating every reversible copy. -/

import D5.S3.ObserverMemory.MultiCopyErasure

namespace D5.S3.ObserverMemory.JointCoherentReversal

open D5.S3.Observer.MeasurementMarginal
open D5.S3.ObserverMemory.MultiCopyErasure
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses
open scoped BigOperators

/- Library-search audit trail (2026-08-12):
   * Local Mathlib searches checked `map_sum`, `map_mul`, `Finset.prod_mul_distrib`,
     `Finset.prod_ite`, and `Complex.I_mul_I`.
   * The restoration proof uses the star operation on complex record amplitudes and finite-product
     simplification; the obstruction proof isolates the squared overlap of one unreversed copy.
   * The finite record channel, overlap model, and qubit witness are imported from the frozen
     `MultiCopyErasure` dependency. That model exposes record vectors, not record unitaries, so the
     theorem is explicitly restricted to overlaps satisfying the displayed unimodularity law. -/

/-- Reverse a record by conjugating each of its complex amplitudes. -/
def reverseRecord (record : EnvironmentRecord) : EnvironmentRecord :=
  fun i a => star (record i a)

/-- Amplitude conjugation conjugates the record's Gram overlap. -/
theorem reverse_record_overlap (record : EnvironmentRecord) (i j : Fin 2) :
    recordOverlap (reverseRecord record) i j = star (recordOverlap record i j) := by
  simp [recordOverlap, reverseRecord, mul_comm]

/-- Apply amplitude conjugation to exactly the selected records of an existing family. -/
def reverseOn {Copy : Type*} [DecidableEq Copy] (copies : Finset Copy)
    (records : Copy -> EnvironmentRecord) : Copy -> EnvironmentRecord :=
  fun k => if k ∈ copies then reverseRecord (records k) else records k

/-- Apply only the reversed records in a selected finite subfamily. -/
noncomputable def reverseChannelOn {Copy : Type*} [DecidableEq Copy]
    (copies : Finset Copy) (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) :
    QubitMatrix :=
  multiRecordChannel
    (fun k : copies => reverseRecord (records k.1)) rho

/--
If every selected overlap is unimodular, the reversed-family channel applied to the output of the
original-family channel restores the chosen matrix entry.
-/
theorem joint_coherent_reversal {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) (i j : Fin 2)
    (hunit : ∀ k, star (recordOverlap (records k) i j) *
      recordOverlap (records k) i j = 1) :
    multiRecordChannel (reverseOn Finset.univ records)
        (multiRecordChannel records rho) i j = rho i j := by
  rw [multi_record_channel_apply, multi_record_channel_apply]
  have hproduct :
      multiRecordOverlap (reverseOn Finset.univ records) i j *
          multiRecordOverlap records i j = 1 := by
    rw [multiRecordOverlap, multiRecordOverlap, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k hk
    simpa [reverseOn, reverse_record_overlap] using hunit k
  rw [← mul_assoc, hproduct, one_mul]

/--
When every copy except `k` is reversed, the composed channel retains exactly the overlap of the
surviving original record at the chosen entry.
-/
theorem one_surviving_copy_composition_apply {Copy : Type*}
    [Fintype Copy] [DecidableEq Copy]
    (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) (i j : Fin 2) (k : Copy)
    (hunit : ∀ l, l ≠ k -> star (recordOverlap (records l) i j) *
      recordOverlap (records l) i j = 1) :
    reverseChannelOn (Finset.univ.erase k) records
        (multiRecordChannel records rho) i j =
      recordOverlap (records k) i j * rho i j := by
  rw [reverseChannelOn, multi_record_channel_apply, multi_record_channel_apply]
  have hproduct :
      multiRecordOverlap
          (fun l : Finset.univ.erase k => reverseRecord (records l.1)) i j *
          multiRecordOverlap records i j =
        recordOverlap (records k) i j := by
    rw [multiRecordOverlap,
      ← Finset.prod_subtype (Finset.univ.erase k) (by simp)
        (fun l => recordOverlap (reverseRecord (records l)) i j), multiRecordOverlap,
      ← Finset.prod_erase_mul Finset.univ (fun l => recordOverlap (records l) i j)
        (Finset.mem_univ k)]
    simp_rw [reverse_record_overlap]
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
    have hrest :
        (∏ l ∈ Finset.univ.erase k,
          star (recordOverlap (records l) i j) * recordOverlap (records l) i j) = 1 := by
      apply Finset.prod_eq_one
      intro l hl
      simpa [reverse_record_overlap] using hunit l (by simpa using hl)
    rw [hrest, one_mul]
  rw [← mul_assoc, hproduct]

/--
For a nonzero input entry, one surviving copy blocks restoration whenever its overlap is not one,
even though every other copy has been amplitude-conjugated.
-/
theorem surviving_copy_blocks_reversal {Copy : Type*}
    [Fintype Copy] [DecidableEq Copy]
    (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) (i j : Fin 2) (k : Copy)
    (hunit : ∀ l, l ≠ k -> star (recordOverlap (records l) i j) *
      recordOverlap (records l) i j = 1)
    (hblock : recordOverlap (records k) i j ≠ 1)
    (hrho : rho i j ≠ 0) :
    reverseChannelOn (Finset.univ.erase k) records
        (multiRecordChannel records rho) i j ≠ rho i j := by
  rw [one_surviving_copy_composition_apply records rho i j k hunit]
  intro hrestored
  have hzero :
      (recordOverlap (records k) i j - 1) * rho i j = 0 := by
    calc
      (recordOverlap (records k) i j - 1) * rho i j =
          recordOverlap (records k) i j * rho i j - rho i j := by ring
      _ = 0 := sub_eq_zero.mpr hrestored
  rcases mul_eq_zero.mp hzero with hfactor | hentry
  · exact hblock (sub_eq_zero.mp hfactor)
  · exact hrho hentry

/--
Two unimodular phase records give a nontrivial composition certificate. Reversing only copy zero
leaves copy one active and fails to restore the original entry; reversing both copies restores it.
-/
theorem two_copy_joint_reversal_certificate :
    let rho := equalSuperpositionDensity
    let phaseRecord : EnvironmentRecord := fun i a =>
      if a = 0 then if i = 0 then 1 else Complex.I else 0
    let records : Fin 2 -> EnvironmentRecord := fun _ => phaseRecord
    let copyZero : Finset (Fin 2) := {0}
    rho 0 1 = 1 / 2 ∧
      multiRecordChannel records rho 0 1 = -(1 / 2) ∧
      reverseChannelOn copyZero records
          (multiRecordChannel records rho) 0 1 = -(Complex.I / 2) ∧
      reverseChannelOn (Finset.univ) records
          (multiRecordChannel records rho) 0 1 = 1 / 2 := by
  simp [equalSuperpositionDensity, reverseChannelOn, multi_record_channel_apply,
    multiRecordOverlap, recordOverlap, reverseRecord]; ring

end D5.S3.ObserverMemory.JointCoherentReversal
