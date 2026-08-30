/- GID: D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyUniqueness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A legal tail rekey is uniquely determined by its document and ledger inputs. -/

import D5.S3.ConceptDynamics.GovernanceFixedPoint.TailRekeyExistence

/- Library-search audit trail (2026-08-30):
   * Exact searches for `legal_tail_rekey_unique` found no declaration in D5,
     pinned Mathlib, or GitHub's indexed Lean sources.
   * Shape searches for `LegalTailRekey`, `RekeyResult`, and uniqueness of a
     function update found only the frozen GFPT carriers and G-D construction.
   * The proof uses structure and function extensionality; no hash axiom or
     independently chosen key is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

/-- Every field of a legal tail rekey is fixed by the old and new ledger inputs. -/
theorem legal_tail_rekey_unique
    {Id : Type u} {Byte : Type v} [DecidableEq Id]
    (tailEligible : Id → Prop)
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (oldEntry : LedgerEntry Id Byte)
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    {first second : RekeyResult Id Byte}
    (hfirst :
      LegalTailRekey tailEligible
        oldDocument newDocument start
        oldEntry active settlement first)
    (hsecond :
      LegalTailRekey tailEligible
        oldDocument newDocument start
        oldEntry active settlement second) :
    first = second := by
  rcases hfirst with
    ⟨_, _, _, _, _, firstPredecessor, firstId, firstBytes, _,
      firstActive, firstSettlement⟩
  rcases hsecond with
    ⟨_, _, _, _, _, secondPredecessor, secondId, secondBytes, _,
      secondActive, secondSettlement⟩
  have predecessorEqual : first.predecessor = second.predecessor :=
    firstPredecessor.trans secondPredecessor.symm
  have entryIdEqual : first.newEntry.logicalId = second.newEntry.logicalId :=
    firstId.trans secondId.symm
  have entryBytesEqual : first.newEntry.bytes = second.newEntry.bytes :=
    firstBytes.trans secondBytes.symm
  have entryEqual : first.newEntry = second.newEntry := by
    cases firstEntryShape : first.newEntry with
    | mk firstEntryId firstEntryBytes =>
      cases secondEntryShape : second.newEntry with
      | mk secondEntryId secondEntryBytes =>
        rw [firstEntryShape, secondEntryShape] at entryIdEqual entryBytesEqual
        have idEqual : firstEntryId = secondEntryId := by
          simpa using entryIdEqual
        have bytesEqual : firstEntryBytes = secondEntryBytes := by
          simpa using entryBytesEqual
        cases idEqual
        cases bytesEqual
        rfl
  have activeEqual : first.newActive = second.newActive := by
    funext logicalId
    rw [firstActive, secondActive, entryEqual]
  have settlementEqual : first.newSettlement = second.newSettlement := by
    funext logicalId
    rw [firstSettlement, secondSettlement]
  cases first
  cases second
  simp_all

#print axioms legal_tail_rekey_unique

-- Concrete elaboration witnesses for domain inhabitance and satisfiable hypotheses.
example : RekeyResult Unit Bool :=
  { predecessor := []
    newEntry := { logicalId := (), bytes := [] }
    newActive := fun _logicalId => []
    newSettlement := fun _logicalId => Verdict.pending }

example :
    ∃ first second : RekeyResult Unit Bool,
      LegalTailRekey (fun _logicalId => True)
          [false] [false, true] 0
          ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
          (fun _logicalId => [false])
          (fun _logicalId => Verdict.pending) first ∧
        LegalTailRekey (fun _logicalId => True)
          [false] [false, true] 0
          ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
          (fun _logicalId => [false])
          (fun _logicalId => Verdict.pending) second := by
  obtain ⟨result, hlegal⟩ := legal_tail_rekey_exists
    (fun _logicalId : Unit => True)
    [false] [false, true] 0
    ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
    (fun _logicalId => [false])
    (fun _logicalId => Verdict.pending)
    trivial ⟨[true], rfl⟩ (Nat.zero_le _) rfl rfl
  exact ⟨result, result, hlegal, hlegal⟩

end D5.S3.ConceptDynamics.GovernanceFixedPoint
