/- GID: D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyConservative
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyConservative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every legal tail rekey preserves settlement and changes only its active source. -/

import D5.S3.ConceptDynamics.GovernanceFixedPoint.TailRekeyExistence

/- Library-search audit trail (2026-08-30):
   * Exact searches for `legal_tail_rekey_is_conservative` found no declaration
     in D5, pinned Mathlib, or GitHub's indexed Lean sources.
   * Shape searches for `ConservativeRekey` found only the frozen GFPT carrier;
     pinned Mathlib supplies the same-point and distinct-point update laws.
   * The proof projects the canonical update and unchanged settlement directly
     from `LegalTailRekey`; it does not test a single sample state. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

/-- A legal tail rekey preserves every settlement and every unrelated active key. -/
theorem legal_tail_rekey_is_conservative
    {Id : Type u} {Byte : Type v} [DecidableEq Id]
    (tailEligible : Id → Prop)
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (oldEntry : LedgerEntry Id Byte)
    (active : ActiveIndex Id Byte)
    (settlement : Settlement Id)
    (result : RekeyResult Id Byte)
    (hlegal :
      LegalTailRekey tailEligible
        oldDocument newDocument start
        oldEntry active settlement result) :
    ConservativeRekey active settlement oldEntry result := by
  rcases hlegal with
    ⟨_, _, _, _, _, predecessor, logicalId, _, _, newActive, newSettlement⟩
  refine ⟨predecessor, logicalId, newSettlement, ?_, ?_⟩
  · intro key
    rw [newActive]
    simp only [ActiveSource, Function.update_self, eq_comm]
  · intro otherId hother
    rw [newActive, Function.update_of_ne hother]

#print axioms legal_tail_rekey_is_conservative

-- Concrete elaboration witnesses for domain inhabitance and satisfiable hypotheses.
example : ConservativeRekey
    (fun _logicalId : Unit => ([] : List Bool))
    (fun _logicalId : Unit => Verdict.pending)
    ({ logicalId := (), bytes := [] } : LedgerEntry Unit Bool)
    ({ predecessor := []
       newEntry := { logicalId := (), bytes := [] }
       newActive := fun _logicalId => []
       newSettlement := fun _logicalId => Verdict.pending } : RekeyResult Unit Bool) := by
  simp [ConservativeRekey, ActiveSource, LedgerEntry.key, contentKey]

example :
    ∃ result : RekeyResult Unit Bool,
      LegalTailRekey (fun _logicalId => True)
          [false] [false, true] 0
          ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
          (fun _logicalId => [false])
          (fun _logicalId => Verdict.pending) result ∧
        ConservativeRekey
          (fun _logicalId => [false])
          (fun _logicalId => Verdict.pending)
          ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
          result := by
  obtain ⟨result, hlegal⟩ := legal_tail_rekey_exists
    (fun _logicalId : Unit => True)
    [false] [false, true] 0
    ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
    (fun _logicalId => [false])
    (fun _logicalId => Verdict.pending)
    trivial ⟨[true], rfl⟩ (Nat.zero_le _) rfl rfl
  exact ⟨result, hlegal,
    legal_tail_rekey_is_conservative
      (fun _logicalId => True)
      [false] [false, true] 0
      ({ logicalId := (), bytes := [false] } : LedgerEntry Unit Bool)
      (fun _logicalId => [false])
      (fun _logicalId => Verdict.pending)
      result hlegal⟩

end D5.S3.ConceptDynamics.GovernanceFixedPoint
