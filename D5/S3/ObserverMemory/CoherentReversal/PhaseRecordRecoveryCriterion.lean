/- GID: D5/S3/ObserverMemory/CoherentReversal/PhaseRecordRecoveryCriterion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/CoherentReversal/PhaseRecordRecoveryCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize finite phase-record recovery and strict residual contraction. -/

import D5.S3.ObserverMemory.JointCoherentReversal

/- Library-search audit trail (2026-08-21):
   * Exact repository hits `joint_coherent_reversal` and
     `surviving_copy_blocks_reversal` are imported and applied directly.
   * The canonical record, overlap, multi-record channel, and reversal operations are reused
     from the frozen observer-memory family; none is redeclared here.
   * Pinned Mathlib hits `Complex.conj_mul'` and `sq_lt_one_iff₀` supply the squared-norm
     factor and its strict contraction. Searches found no existing theorem combining all three
     recovery clauses or the strict original-then-conjugate channel calculation. -/

namespace D5.S3.ObserverMemory.CoherentReversal.PhaseRecordRecoveryCriterion

open D5.S3.Observer.MeasurementMarginal
open D5.S3.ObserverMemory.MultiCopyErasure
open D5.S3.ObserverMemory.JointCoherentReversal
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

/-- A finite record family has three complementary recovery behaviors at a selected entry:
all unit-modulus overlaps are jointly reversible; any strict overlap contraction leaves its
squared modulus after the matching conjugate channel and cannot restore a nonzero entry; and one
unreversed nontrivial copy blocks recovery when every other copy is unimodular. -/
theorem phase_record_recovery_criterion
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (records : Copy -> EnvironmentRecord) (rho : QubitMatrix) (i j : Fin 2) :
    ((forall k, ‖recordOverlap (records k) i j‖ = 1) ->
      multiRecordChannel (reverseOn Finset.univ records)
          (multiRecordChannel records rho) i j = rho i j) ∧
    ((exists k, ‖recordOverlap (records k) i j‖ < 1) ->
      exists k,
        ‖recordOverlap (records k) i j‖ < 1 ∧
        ‖recordOverlap (records k) i j‖ ^ 2 < 1 ∧
        recordChannel (reverseRecord (records k))
            (recordChannel (records k) rho) i j =
          (‖recordOverlap (records k) i j‖ : ℂ) ^ 2 * rho i j ∧
        (rho i j ≠ 0 ->
          recordChannel (reverseRecord (records k))
              (recordChannel (records k) rho) i j ≠ rho i j)) ∧
    (forall k,
      (forall l, l ≠ k -> ‖recordOverlap (records l) i j‖ = 1) ->
      recordOverlap (records k) i j ≠ 1 ->
      rho i j ≠ 0 ->
      reverseChannelOn (Finset.univ.erase k) records
          (multiRecordChannel records rho) i j ≠ rho i j) := by
  constructor
  · intro hall
    apply joint_coherent_reversal
    intro k
    calc
      star (recordOverlap (records k) i j) * recordOverlap (records k) i j =
          (‖recordOverlap (records k) i j‖ : ℂ) ^ 2 := by
        simpa only [starRingEnd_apply] using
          Complex.conj_mul' (recordOverlap (records k) i j)
      _ = 1 := by rw [hall k]; norm_num
  constructor
  · rintro ⟨k, hk⟩
    have hsq : ‖recordOverlap (records k) i j‖ ^ 2 < 1 :=
      (sq_lt_one_iff₀ (norm_nonneg _)).2 hk
    have hfactor :
        star (recordOverlap (records k) i j) * recordOverlap (records k) i j =
          (‖recordOverlap (records k) i j‖ : ℂ) ^ 2 := by
      simpa only [starRingEnd_apply] using
        Complex.conj_mul' (recordOverlap (records k) i j)
    have hchannel :
        recordChannel (reverseRecord (records k))
            (recordChannel (records k) rho) i j =
          (‖recordOverlap (records k) i j‖ : ℂ) ^ 2 * rho i j := by
      simp only [recordChannel, reverse_record_overlap]
      rw [← mul_assoc, hfactor]
    refine ⟨k, hk, hsq, hchannel, ?_⟩
    intro hrho
    rw [hchannel]
    intro hrestored
    have hzero :
        ((‖recordOverlap (records k) i j‖ : ℂ) ^ 2 - 1) * rho i j = 0 := by
      calc
        ((‖recordOverlap (records k) i j‖ : ℂ) ^ 2 - 1) * rho i j =
            (‖recordOverlap (records k) i j‖ : ℂ) ^ 2 * rho i j - rho i j := by
          ring
        _ = 0 := sub_eq_zero.mpr hrestored
    rcases mul_eq_zero.mp hzero with hsqzero | hentry
    · have hone : ‖recordOverlap (records k) i j‖ ^ 2 = 1 := by
        exact_mod_cast sub_eq_zero.mp hsqzero
      exact (ne_of_lt hsq) hone
    · exact hrho hentry
  · intro k hother hblock hrho
    apply surviving_copy_blocks_reversal records rho i j k _ hblock hrho
    intro l hl
    calc
      star (recordOverlap (records l) i j) * recordOverlap (records l) i j =
          (‖recordOverlap (records l) i j‖ : ℂ) ^ 2 := by
        simpa only [starRingEnd_apply] using
          Complex.conj_mul' (recordOverlap (records l) i j)
      _ = 1 := by rw [hother l hl]; norm_num

/-- The unit-modulus and strict-contraction antecedents both have checked canonical witnesses. -/
example :
    (forall k : Unit,
      ‖recordOverlap ((fun _ : Unit => addressIndependentRecord) k) 0 1‖ = 1) ∧
    (exists k : Unit,
      ‖recordOverlap ((fun _ : Unit => copiedAddressRecord) k) 0 1‖ < 1) ∧
    equalSuperpositionDensity 0 1 ≠ 0 := by
  simp [addressIndependentRecord, copiedAddressRecord, recordOverlap,
    equalSuperpositionDensity]

/-- The finite copy domain used by the checked witnesses is inhabited. -/
example : Unit := ()

#print axioms phase_record_recovery_criterion

end D5.S3.ObserverMemory.CoherentReversal.PhaseRecordRecoveryCriterion
