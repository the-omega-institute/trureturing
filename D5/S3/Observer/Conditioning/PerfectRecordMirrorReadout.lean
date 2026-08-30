/- GID: D5/S3/Observer/Conditioning/PerfectRecordMirrorReadout
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/PerfectRecordMirrorReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A perfect unread record erases observables with vanishing record-diagonal blocks. -/

import D5.S3.Observer.Conditioning

/- Library-search audit trail (2026-08-30):
   * Exact repository primitives inspected: `IsRecordMeasurement` and `unreadState` in
     `D5/S3/Observer/Conditioning.lean:19-25`; `unreadState_idempotent` and
     `unreadState_fixed_iff` in the same file; `environment_marginal_channel` in
     `D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel.lean:29`; and the four-point
     orbit identity `off_line_zero_orbit_sum_eq_four_mul_re` in
     `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits.lean:59`.
   * Body-shape search for a packaged theorem proving a trace pairing against a
     record-diagonal-free observable: `rg -n 'trace.*P.*J|trace.*zero|off.?diagonal.*trace'
     D5/S3 --glob '*.lean'` found no public exact hit. The private calculation in
     `Observer/Conditioning/UnreadStateOrthogonalProjection.lean:36` was inspected but is
     not reusable across namespaces, so the trace-cyclic steps are written inline here.
   * Pinned Mathlib search for a finite pinching/trace-annihilation theorem: `rg -n
     'trace.*cycle|trace.*mul_comm|pinching|off.?diagonal' .lake/packages/mathlib/Mathlib`
     found only the generic trace identities, which are applied directly below.
   * No new definition or abbreviation is introduced; all objects use the canonical
     `IsRecordMeasurement` and `unreadState` primitives.
-/

open scoped BigOperators

namespace D5.S3.Observer.Conditioning.PerfectRecordMirrorReadout

open D5.S3.Observer.Conditioning

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa]
    {P : kappa -> Matrix n n ℂ}

/-- Perfectly recording a finite label and discarding it annihilates the expectation
of any observable whose diagonal record blocks vanish. -/
theorem perfect_record_mirror_readout_zero
    (hP : IsRecordMeasurement P) (rho J : Matrix n n ℂ)
    (hDiagonal : forall k, P k * J * P k = 0) :
    Matrix.trace (unreadState P rho * J) = 0 /\
      Matrix.trace (unreadState P rho) = Matrix.trace rho := by
  classical
  constructor
  · rw [unreadState, Matrix.sum_mul, Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro k hk
    calc
      Matrix.trace ((P k * rho * P k) * J) =
          Matrix.trace (P k * rho * (P k * J)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((P k * J) * P k * rho) :=
        Matrix.trace_mul_cycle (P k) rho (P k * J)
      _ = Matrix.trace (rho * ((P k * J) * P k)) :=
        Matrix.trace_mul_comm ((P k * J) * P k) rho
      _ = Matrix.trace (rho * (P k * J * P k)) := by rfl
      _ = Matrix.trace (rho * 0) := by rw [hDiagonal k]
      _ = 0 := by simp
  · exact unreadState_trace hP rho

/-- A nonzero unread cross-readout forces a nonzero record-diagonal block of its
observable, so it cannot coexist with the perfect-record hypothesis above. -/
theorem perfect_record_nonzero_readout_incompatible
    (hP : IsRecordMeasurement P) (rho J : Matrix n n ℂ)
    (hReadout : Matrix.trace (unreadState P rho * J) ≠ 0) :
    exists k, P k * J * P k ≠ 0 := by
  classical
  by_contra hAll
  apply hReadout
  exact (perfect_record_mirror_readout_zero hP rho J (fun k => by
    by_contra hBlock
    exact hAll ⟨k, hBlock⟩)).1

#print axioms perfect_record_mirror_readout_zero
#print axioms perfect_record_nonzero_readout_incompatible

end D5.S3.Observer.Conditioning.PerfectRecordMirrorReadout
