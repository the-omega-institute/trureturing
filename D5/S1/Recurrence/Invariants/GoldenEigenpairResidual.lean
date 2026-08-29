/- GID: D5/S1/Recurrence/Invariants/GoldenEigenpairResidual
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/GoldenEigenpairResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Shift iteration exposes the golden eigenpair and the exact contracting residual. -/

import D5.S1.Recurrence.BilateralLiftUniqueness

/- Library-search audit trail (2026-08-29):
   * Exact frozen hits `shift_golden_eigenvectors` and
     `fibonacci_weight_residual` supply the one-step eigenlaws and residual.
   * Current-tree name and body-shape searches found no public theorem evaluating
     both iterated eigenlines at zero as the source pair while also exposing the
     Fibonacci residual in the same statement.
   * Pinned Mathlib supplies `Function.iterate_succ_apply'` and linear-map scalar
     transport. No exact golden-eigenpair aggregate was found; `loogle` and
     `leansearch` are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.GoldenEigenpairResidual

open D5.S1.Recurrence

/-- Iterating the canonical forward shift on the two frozen eigenlines and
evaluating at index zero gives the golden power pair. The same public clause
records the Fibonacci one-step deficit as the contracting coordinate. -/
theorem golden_eigenpair_and_fibonacci_residual :
    forall k : Nat,
      ((((shift : Seq -> Seq)^[k]) expandingSequence) 0,
          (((shift : Seq -> Seq)^[k]) contractingSequence) 0) =
        (Real.goldenRatio ^ (k + 1), Real.goldenConj ^ (k + 1)) ∧
      fibonacciWeight (k + 1) - Real.goldenRatio * fibonacciWeight k =
        Real.goldenConj ^ (k + 1) := by
  have expanding_iterate : forall n : Nat,
      (((shift : Seq -> Seq)^[n]) expandingSequence) =
        Real.goldenRatio ^ n • expandingSequence := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, map_smul,
          shift_golden_eigenvectors.1, smul_smul, <- pow_succ]
  have contracting_iterate : forall n : Nat,
      (((shift : Seq -> Seq)^[n]) contractingSequence) =
        Real.goldenConj ^ n • contractingSequence := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, map_smul,
          shift_golden_eigenvectors.2, smul_smul, <- pow_succ]
  intro k
  constructor
  · rw [expanding_iterate, contracting_iterate]
    simp [expandingSequence, contractingSequence, pow_succ]
  · exact fibonacci_weight_residual k

#print axioms golden_eigenpair_and_fibonacci_residual

end D5.S1.Recurrence.Invariants.GoldenEigenpairResidual
