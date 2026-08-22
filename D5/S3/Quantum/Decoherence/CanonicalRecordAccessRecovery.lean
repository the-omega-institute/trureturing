/- GID: D5/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Express reversible record recovery through the canonical copied-address record. -/

/- Library-search audit trail (2026-08-22):
   * Repository search found the family source of truth
     `D5.S3.Observer.MeasurementMarginal.copiedAddressRecord`; it is imported and used directly.
   * The exact repository theorem
     `ReducedRecordAccessDefect.reduced_irreversibility_is_access_defect` proves all eight
     operational conclusions over an extensionally equal record with flipped equality syntax.
   * No second packaged theorem over the canonical record was found. The exact theorem is applied
     through the explicit public bridge below; no source primitive or proof is redeclared. -/

import D5.S3.Observer.MeasurementMarginal
import D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect

namespace D5.S3.Quantum.Decoherence.CanonicalRecordAccessRecovery

open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The canonical copied-address record is extensionally equal to the predecessor's record,
whose defining equality was written in the opposite orientation. -/
theorem canonical_copied_address_record_eq_prior :
    D5.S3.Observer.MeasurementMarginal.copiedAddressRecord =
      D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.copiedAddressRecord := by
  funext i a
  simp [D5.S3.Observer.MeasurementMarginal.copiedAddressRecord,
    D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.copiedAddressRecord, eq_comm]

/-- A reversible controlled coupling writes the canonical copied-address record while retaining
the phase-bearing distinction globally. Tracing that record identifies the two reduced states,
so no reduced-state function recovers both joint records; controlling the record and applying
the adjoint coupling nevertheless restores each blank-record input exactly. -/
theorem reduced_irreversibility_is_canonical_record_access_defect
    (rho sigma : QubitMatrix)
    (hdiag : ∀ i, rho i i = sigma i i)
    (hcoherence : ∃ i j, i ≠ j ∧ rho i j ≠ sigma i j) :
    D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.copyUnitary ∈
        Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ ∧
      unitaryEvolution
          D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.copyUnitary
          (D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.blankEnvironmentJointState rho) =
        controlledRecordJointState
          D5.S3.Observer.MeasurementMarginal.copiedAddressRecord rho ∧
      unitaryEvolution
          D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.copyUnitary
          (D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.blankEnvironmentJointState sigma) =
        controlledRecordJointState
          D5.S3.Observer.MeasurementMarginal.copiedAddressRecord sigma ∧
      traceEnvironment
          (controlledRecordJointState
            D5.S3.Observer.MeasurementMarginal.copiedAddressRecord rho) =
        traceEnvironment
          (controlledRecordJointState
            D5.S3.Observer.MeasurementMarginal.copiedAddressRecord sigma) ∧
      controlledRecordJointState
          D5.S3.Observer.MeasurementMarginal.copiedAddressRecord rho ≠
        controlledRecordJointState
          D5.S3.Observer.MeasurementMarginal.copiedAddressRecord sigma ∧
      (¬ ∃ recover : QubitMatrix → JointQubitEnvironmentMatrix,
        recover
            (traceEnvironment
              (controlledRecordJointState
                D5.S3.Observer.MeasurementMarginal.copiedAddressRecord rho)) =
            controlledRecordJointState
              D5.S3.Observer.MeasurementMarginal.copiedAddressRecord rho ∧
          recover
              (traceEnvironment
                (controlledRecordJointState
                  D5.S3.Observer.MeasurementMarginal.copiedAddressRecord sigma)) =
            controlledRecordJointState
              D5.S3.Observer.MeasurementMarginal.copiedAddressRecord sigma) ∧
      unitaryEvolution
          (star D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.copyUnitary)
          (controlledRecordJointState
            D5.S3.Observer.MeasurementMarginal.copiedAddressRecord rho) =
        D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.blankEnvironmentJointState rho ∧
      unitaryEvolution
          (star D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.copyUnitary)
          (controlledRecordJointState
            D5.S3.Observer.MeasurementMarginal.copiedAddressRecord sigma) =
        D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.blankEnvironmentJointState sigma := by
  rw [canonical_copied_address_record_eq_prior]
  rcases
      D5.S3.Quantum.Decoherence.ReducedRecordAccessDefect.reduced_irreversibility_is_access_defect
        rho sigma hdiag hcoherence with
    ⟨hunitary, ⟨hrho, hsigma⟩, htrace, hjoint, hdecoder, ⟨hrecoverRho, hrecoverSigma⟩⟩
  exact ⟨hunitary, hrho, hsigma, htrace, hjoint, hdecoder, hrecoverRho, hrecoverSigma⟩

/- These concrete matrices witness that the source hypotheses and carrier are inhabited. -/
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

#print axioms canonical_copied_address_record_eq_prior
#print axioms reduced_irreversibility_is_canonical_record_access_defect

end D5.S3.Quantum.Decoherence.CanonicalRecordAccessRecovery
