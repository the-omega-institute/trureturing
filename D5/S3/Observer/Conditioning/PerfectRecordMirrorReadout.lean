/- GID: D5/S3/Observer/Conditioning/PerfectRecordMirrorReadout
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/PerfectRecordMirrorReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A perfect unread record erases observables with vanishing record-diagonal blocks. -/

import D5.S3.Observer.Conditioning
import D5.S3.Observer.MeasurementMarginal

/- Library-search audit trail (2026-08-30):
   * Exact repository primitives inspected: `QubitMatrix` and `qubitX` in
     `D5/S3/Quantum/FiniteDimensional.lean`, `unreadState` in
     `D5/S3/Observer/Conditioning.lean`, and `addressProjection` in
     `D5/S3/Observer/MeasurementMarginal.lean`. They supply the source's two-address
     carrier, swap observable, unread channel, and standard address projectors.
   * Body-shape search for a packaged theorem proving a trace pairing against a
     record-diagonal-free observable: `rg -n 'trace.*P.*J|trace.*zero|off.?diagonal.*trace'
     D5/S3 --glob '*.lean'` found no public exact hit. The private calculation in
     `Observer/Conditioning/UnreadStateOrthogonalProjection.lean:36` was inspected but is
     not reusable across namespaces, so the trace-cyclic steps are written inline here.
   * Pinned Mathlib search for a finite pinching/trace-annihilation theorem found only
     generic trace identities, which are applied directly below. GitHub Lean-code
     queries for the source's observer-ontology predicates returned no results.
   * No new definition or abbreviation is introduced; all objects use the canonical
     `unreadState`, `addressProjection`, and `qubitX` primitives.
-/

open scoped BigOperators

namespace D5.S3.Observer.Conditioning.PerfectRecordMirrorReadout

open D5.S3.Observer.Conditioning
open D5.S3.Observer.MeasurementMarginal
open D5.S3.Quantum.FiniteDimensional

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n kappa : Type*} [Fintype n]
    [Fintype kappa]
    {P : kappa -> Matrix n n ℂ}

/-- A finite unread pinching annihilates the trace pairing with an observable whose
record-diagonal blocks vanish. -/
theorem unread_state_trace_pairing_eq_zero
    (rho J : Matrix n n ℂ)
    (hDiagonal : forall k, P k * J * P k = 0) :
    Matrix.trace (unreadState P rho * J) = 0 := by
  classical
  rw [unreadState, Matrix.sum_mul, Matrix.trace_sum]
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

/-- Discarding the perfectly recorded left/right address makes the expectation of
the fixed mirror-swap observable vanish. -/
theorem perfect_record_mirror_readout_zero (rho : QubitMatrix) :
    Matrix.trace (unreadState addressProjection rho * qubitX) = 0 := by
  apply unread_state_trace_pairing_eq_zero
  intro k
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [addressProjection, qubitX, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms unread_state_trace_pairing_eq_zero
#print axioms perfect_record_mirror_readout_zero

end D5.S3.Observer.Conditioning.PerfectRecordMirrorReadout
