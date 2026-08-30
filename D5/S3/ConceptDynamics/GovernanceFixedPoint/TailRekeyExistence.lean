/- GID: D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyExistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every eligible active tail has a legal rekey along a document prefix extension. -/

import D5.S3.ConceptDynamics.GovernanceFixedPoint.TailSpanPrefixExtension

/- Library-search audit trail (2026-08-30):
   * Exact searches for `legal_tail_rekey_exists` found no declaration in D5
     or pinned Mathlib.
   * Shape searches for `LegalTailRekey`, `RekeyResult`, and the required
     active-index update found only their declarations in the frozen GFPT Core.
   * The construction uses those canonical carriers and discharges its tail
     prefix clause with `tail_span_prefix_extension`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

/-- Replacing an eligible active tail by the extended tail gives a legal rekey. -/
theorem legal_tail_rekey_exists
    {Id : Type u} {Byte : Type v} [DecidableEq Id]
    (tailEligible : Id → Prop)
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (oldEntry : LedgerEntry Id Byte)
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    (heligible : tailEligible oldEntry.logicalId)
    (hprefix : PrefixExtension oldDocument newDocument)
    (hstart : start ≤ oldDocument.length)
    (hbytes : oldEntry.bytes = TailBytes oldDocument start)
    (hactive :
      ActiveSource active oldEntry.logicalId oldEntry.key) :
    ∃ result : RekeyResult Id Byte,
      LegalTailRekey tailEligible
        oldDocument newDocument start
        oldEntry active settlement result := by
  let newEntry : LedgerEntry Id Byte :=
    { logicalId := oldEntry.logicalId
      bytes := TailBytes newDocument start }
  let result : RekeyResult Id Byte :=
    { predecessor := oldEntry.key
      newEntry := newEntry
      newActive := Function.update active oldEntry.logicalId newEntry.key
      newSettlement := settlement }
  refine ⟨result, heligible, hprefix, hstart, hbytes, hactive, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simpa only [result, newEntry, hbytes] using
      tail_span_prefix_extension oldDocument newDocument start hprefix hstart
  · rfl
  · rfl

#print axioms legal_tail_rekey_exists

-- Concrete elaboration witnesses for domain inhabitance and satisfiable hypotheses.
example : RekeyResult Unit Bool :=
  { predecessor := []
    newEntry := { logicalId := (), bytes := [] }
    newActive := fun _logicalId => []
    newSettlement := fun _logicalId => Verdict.pending }

example :
    ∃ result : RekeyResult Unit Bool,
      LegalTailRekey (fun _logicalId => True)
        [false] [false, true] 0
        ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
        (fun _logicalId => [false])
        (fun _logicalId => Verdict.pending) result := by
  exact legal_tail_rekey_exists
    (fun _logicalId => True)
    [false] [false, true] 0
    ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
    (fun _logicalId => [false])
    (fun _logicalId => Verdict.pending)
    trivial ⟨[true], rfl⟩ (Nat.zero_le _) rfl rfl

end D5.S3.ConceptDynamics.GovernanceFixedPoint
