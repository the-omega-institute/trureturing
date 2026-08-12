/- GID: D5/S3/ObserverMemory/LedgerEnvironmentBridge
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/LedgerEnvironmentBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the strongest frozen record/environment bridge available without ledger fiat. -/

/- Library-search audit trail (2026-08-12):
   * The frozen history carrier has no map from an event opcode to an environment record;
     introducing one here would postulate, rather than prove, the requested identification.
   * `MultiCopyErasure.multiRecordChannel` is the frozen finite record-channel composition.
   * `EnvironmentRecords.trace_environment_controlled_record_eq_phase_damping` is the public
     frozen bridge from a controlled environment interaction to decoherence.
   * `QubitWitnesses.phaseDampingIterate_apply` supplies the independently frozen iterated
     decoherence normalization used for the finite-family identification. -/

import D5.S3.ObserverMemory.MultiCopyErasure

namespace D5.S3.ObserverMemory.LedgerEnvironmentBridge

open D5.S3.Observer.MeasurementMarginal
open D5.S3.ObserverMemory.MultiCopyErasure
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

/-- A one-entry instance of the frozen finite record channel is exactly the system marginal
of the independently frozen controlled environment interaction. The Gram premise is the
normalization that selects the corresponding phase-damping coefficient. -/
theorem one_record_channel_is_environment_marginal
    (record : EnvironmentRecord) (c : DampingCoefficient)
    (rho : QubitMatrix)
    (hGram : ∀ i j, recordOverlap record i j =
      if i = j then 1 else ((c : ℝ) : ℂ)) :
    traceEnvironment (controlledRecordJointState record rho) =
      multiRecordChannel (fun _ : Unit => record) rho := by
  rw [trace_environment_controlled_record_eq_phase_damping record c rho hGram]
  funext i j
  rw [multi_record_channel_apply]
  simp [multiRecordOverlap, hGram, phaseDamping]

/-- Composition over `N` entries of an existing normalized record family is exactly `N`
iterations of the independently frozen decoherence channel with the same Gram coefficient. -/
theorem finite_record_channel_is_iterated_decoherence
    (record : EnvironmentRecord) (c : DampingCoefficient)
    (N : ℕ) (rho : QubitMatrix)
    (hGram : ∀ i j, recordOverlap record i j =
      if i = j then 1 else ((c : ℝ) : ℂ)) :
    multiRecordChannel (fun _ : Fin N => record) rho =
      phaseDampingIterate c N rho := by
  funext i j
  rw [multi_record_channel_apply, phaseDampingIterate_apply]
  simp [multiRecordOverlap, hGram]

/-- For two copied-address records, the two frozen constructions agree on the same
equal-superposition input, preserve both populations, and erase both coherences. -/
theorem record_decoherence_anti_vacuity :
    let zeroDamping : DampingCoefficient := ⟨0, by constructor <;> norm_num⟩
    let rho := equalSuperpositionDensity
    let recordOutput :=
      multiRecordChannel (fun _ : Fin 2 => copiedAddressRecord) rho
    let decoherenceOutput := phaseDampingIterate zeroDamping 2 rho
    traceEnvironment (controlledRecordJointState copiedAddressRecord rho) =
        multiRecordChannel (fun _ : Unit => copiedAddressRecord) rho ∧
      recordOutput = decoherenceOutput ∧
      recordOutput 0 0 = 1 / 2 ∧
      recordOutput 1 1 = 1 / 2 ∧
      recordOutput 0 1 = 0 ∧
      recordOutput 1 0 = 0 := by
  dsimp
  have hGram : ∀ i j, recordOverlap copiedAddressRecord i j =
      if i = j then 1 else (((0 : ℝ) : ℂ)) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [recordOverlap, copiedAddressRecord]
  refine ⟨one_record_channel_is_environment_marginal copiedAddressRecord
    ⟨0, by constructor <;> norm_num⟩
    equalSuperpositionDensity hGram, ?_⟩
  refine ⟨finite_record_channel_is_iterated_decoherence copiedAddressRecord
    ⟨0, by constructor <;> norm_num⟩ 2 equalSuperpositionDensity hGram, ?_⟩
  simp [multi_record_channel_apply, multiRecordOverlap, recordOverlap,
    copiedAddressRecord, equalSuperpositionDensity]

end D5.S3.ObserverMemory.LedgerEnvironmentBridge
