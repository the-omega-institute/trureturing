/- GID: D5/S3/Quantum/Measurement/PerfectRecordExchangeReadout
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/PerfectRecordExchangeReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Perfect copied-address recording eliminates the unread exchange readout. -/

import D5.S3.Observer.MeasurementMarginal

/- Library-search audit trail (2026-08-30):
   * D5 searches for copied-record marginals, unread pinching, off-diagonal
     vanishing, and exchange-observable traces found no theorem containing the
     whole result. `MeasurementMarginal` supplies the canonical copied record,
     controlled joint state, environment trace, and off-diagonal marginal law.
   * Pinned Mathlib searches for pinching, dephasing, off-diagonal trace
     pairings, and exchange matrices found generic matrix infrastructure but no
     exact copied-record exchange-expectation result.
   * A reachable third-party Lean search found pure-state dephasing results in
     `zblore/csd-lean4`, but no result on this arbitrary two-address matrix
     carrier or with the unread-interface and joint-record clauses below.
   * Body-shape searches found `qubitX`, `controlledRecordJointState`,
     `traceEnvironment`, `copiedAddressRecord`, and the copied-record marginal
     theorems. They are imported directly; this module introduces no new
     definition or private declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.PerfectRecordExchangeReadout

open D5.S3.Observer.MeasurementMarginal
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional

/-- Perfectly copying the two-address label into a record and then tracing that
record out makes the exchange-observable expectation zero. Consequently a
nonzero exchange-type readout cannot be the same function on this unread
marginal. If the input has off-diagonal coherence, the controlled joint state
retains it between matched system-record addresses while the unread marginal
does not. -/
theorem perfect_record_exchange_readout_vanishes (rho : QubitMatrix) :
    let jointState := controlledRecordJointState copiedAddressRecord rho
    let unreadMarginal := traceEnvironment jointState
    Matrix.trace (unreadMarginal * qubitX) = 0 ∧
      (¬ Matrix.trace (unreadMarginal * qubitX) ≠ 0) ∧
      (∀ i j : Fin 2, i ≠ j → rho i j ≠ 0 →
        jointState (i, i) (j, j) ≠ 0 ∧ unreadMarginal i j = 0) ∧
      (∀ readout : QubitMatrix → ℂ, readout unreadMarginal ≠ 0 →
        readout ≠ fun sigma => Matrix.trace (sigma * qubitX)) := by
  dsimp only
  have h01 :
      traceEnvironment (controlledRecordJointState copiedAddressRecord rho) 0 1 = 0 :=
    copied_record_partial_trace_offDiagonal_eq_zero rho 0 1 (by decide)
  have h10 :
      traceEnvironment (controlledRecordJointState copiedAddressRecord rho) 1 0 = 0 :=
    copied_record_partial_trace_offDiagonal_eq_zero rho 1 0 (by decide)
  have hExchange :
      Matrix.trace
          (traceEnvironment (controlledRecordJointState copiedAddressRecord rho) * qubitX) = 0 := by
    simp [Matrix.trace, Matrix.mul_apply, qubitX, Fin.sum_univ_two, h01, h10]
  refine ⟨hExchange, by simp [hExchange], ?_, ?_⟩
  · intro i j hij hCoherence
    constructor
    · simpa [controlledRecordJointState, copiedAddressRecord] using hCoherence
    · exact copied_record_partial_trace_offDiagonal_eq_zero rho i j hij
  · intro readout hNonzero hSame
    rw [hSame] at hNonzero
    exact hNonzero hExchange

#print axioms perfect_record_exchange_readout_vanishes

end D5.S3.Quantum.Measurement.PerfectRecordExchangeReadout
