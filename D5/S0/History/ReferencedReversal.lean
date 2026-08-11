/- GID: D5/S0/History/ReferencedReversal
   generality: G
   mirror-B: D5/B/S0/History/ReferencedReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integer ledgers admit exact reversal with references on every negative coordinate. -/

import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/- Provenance: the group-completion coordinate equivalence is pinned Mathlib's
   `FreeAbelianGroup.equivFinsupp`; reversal support uses
   `Finsupp.support_neg`. The referenced event structure is repository-local. -/

namespace D5.S0.History.ReferencedReversal

/-- A group-completed ledger is a finitely supported integer-valued family. -/
abbrev GroupLedger (Address : Type*) := Finsupp Address ℤ

/-- Integer-coordinate ledgers are the standard coordinate realization of the
free abelian group on the address type. -/
noncomputable def groupLedgerEquiv (Address : Type*) :
    FreeAbelianGroup Address ≃+ GroupLedger Address :=
  FreeAbelianGroup.equivFinsupp Address

/-- A ledger event whose negative coordinates are required to carry an audit
reference. The reference set may express a richer provenance relation than a
single global event identifier. -/
structure ReversalEvent (Address Ref : Type*) where
  delta : GroupLedger Address
  references : Address -> Set Ref
  negative_referenced : forall address, delta address < 0 -> (references address).Nonempty

/-- Reverse an entry by coordinatewise negation and attach the supplied
per-address reference exactly at its negative coordinates. -/
noncomputable def reversal {Address Ref : Type*} (reference : Address -> Ref)
    (entry : GroupLedger Address) : ReversalEvent Address Ref where
  delta := -entry
  references := fun address =>
    if -entry address < 0 then {reference address} else ∅
  negative_referenced := by
    intro address hnegative
    have hpositive : 0 < entry address := by simpa using hnegative
    simp [hpositive]

/-- The integer ledger is a faithful free-abelian-group coordinate system.
Reversal maps a group element to its negated coordinates, cancels the original
entry, preserves its finite support, and has a nonempty reference set exactly
at the negative reversal coordinates. -/
theorem group_ledger_reversal_spec {Address Ref : Type*}
    (reference : Address -> Ref) (entry : FreeAbelianGroup Address) :
    Function.Bijective (groupLedgerEquiv Address) ∧
      groupLedgerEquiv Address (-entry) =
        (reversal reference (groupLedgerEquiv Address entry)).delta ∧
      groupLedgerEquiv Address entry +
        (reversal reference (groupLedgerEquiv Address entry)).delta = 0 ∧
      (reversal reference (groupLedgerEquiv Address entry)).delta.support =
        (groupLedgerEquiv Address entry).support ∧
      forall address,
        ((reversal reference (groupLedgerEquiv Address entry)).references address).Nonempty ↔
          (reversal reference (groupLedgerEquiv Address entry)).delta address < 0 := by
  refine ⟨(groupLedgerEquiv Address).bijective, ?_, ?_, ?_, ?_⟩
  · simp [reversal]
  · simp [reversal]
  · simp [reversal]
  · intro address
    by_cases hpositive : 0 < (groupLedgerEquiv Address entry) address <;>
      simp [reversal, hpositive]

end D5.S0.History.ReferencedReversal
