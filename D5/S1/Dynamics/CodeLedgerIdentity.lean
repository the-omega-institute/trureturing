/- GID: D5/S1/Dynamics/CodeLedgerIdentity
   generality: I
   mirror-B: D5/B/S1/Dynamics/CodeLedgerIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical code and ledger equality exactly determine state identity. -/

import D5.S1.Digit.PrimeAxisEncoding

/- Provenance: repository-local composition of the canonical prime-axis encoding
   equivalence with pinned Mathlib's `Equiv.apply_eq_iff_eq` and generated
   structure-constructor injectivity. -/

namespace D5.S1.Dynamics.CodeLedgerIdentity

open D5.S1.Digit

/-- A state whose mathematical coordinate is recorded together with its ledger. -/
structure CodeLedgerState (Ledger : Type*) where
  coordinate : PrimeAxisTable
  ledger : Ledger

/-- The canonical positive-natural code of the state's prime-axis coordinate. -/
noncomputable def canonicalCode {Ledger : Type*}
    (state : CodeLedgerState Ledger) : ℕ+ :=
  primeAxisEncoding state.coordinate

/-- Two states are identical exactly when both their canonical codes and ledger
coordinates agree. -/
theorem same_state_iff_same_code_and_ledger {Ledger : Type*}
    (left right : CodeLedgerState Ledger) :
    left = right ↔
      canonicalCode left = canonicalCode right ∧ left.ledger = right.ledger := by
  cases left
  cases right
  simp only [canonicalCode, CodeLedgerState.mk.injEq, Equiv.apply_eq_iff_eq]

end D5.S1.Dynamics.CodeLedgerIdentity
