/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/TargetChangeSettlementConservation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/TargetChangeSettlementConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Append-only versioned commitments preserve pure settlement at every old round. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-26):
   * `rg -n -i 'TargetChange|target_change|SettleAt|settle_at|AppendOnly|
     append_only_old_settlement|RoundRecord|VersionEdge' D5 --glob '*.lean'`
     found only the adjacent `AppendOnlyAnswerabilityMonotonicity` module;
     it proves answer-set refinement, not settlement lookup preservation.
   * The same shape query in pinned Mathlib found no target-change, settlement,
     or append-only commitment theorem.  `List.get?_append` is the library
     primitive used by the proof.
   * The source's `ProspectiveCommitment` and `AppendOnlyExtension` occur only
     in the theory text, not as Lean declarations; this module supplies the
     faithful finite ledger bridge without inventing their omitted machinery.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/-- A target revision records a new version edge and its audit metadata. -/
structure TargetChange
    (Target Reason Author Time Round : Type u) where
  fromTarget : Target
  toTarget : Target
  reason : Reason
  author : Author
  time : Time
  affectedRounds : Set Round

/-- The source's version edge is the existence of a recorded target change. -/
def VersionEdge
    {Target Reason Author Time Round : Type u}
    (fromTarget toTarget : Target) : Prop :=
  ∃ change : TargetChange Target Reason Author Time Round,
    change.fromTarget = fromTarget ∧ change.toTarget = toTarget

theorem target_change_is_version_edge
    {Target Reason Author Time Round : Type u}
    (change : TargetChange Target Reason Author Time Round) :
    VersionEdge (Reason := Reason) (Author := Author) (Time := Time) (Round := Round)
      change.fromTarget change.toTarget := by
  exact ⟨change, rfl, rfl⟩

/-- One immutable round record contains its target version, commitment, and evidence. -/
structure RoundRecord
    (Target Commitment Evidence : Type u) where
  target : Target
  commitment : Commitment
  evidence : Evidence

/-- Later ledger states are obtained by appending a tail to the old ledger. -/
def AppendOnly
    {Target Commitment Evidence : Type u}
    (old new : List (RoundRecord Target Commitment Evidence)) : Prop :=
  ∃ tail, new = old ++ tail

/-- Purely evaluate the commitment and evidence stored at one ledger index. -/
def settleAt
    {Target Commitment Evidence Verdict : Type u}
    (evaluate : Commitment → Evidence → Verdict)
    (ledger : List (RoundRecord Target Commitment Evidence))
    (round : Nat) : Option Verdict :=
  (ledger[round]?).map (fun record => evaluate record.commitment record.evidence)

/-- Appending only later versions cannot change the pure settlement of an old round. -/
theorem append_only_old_settlement_unchanged
    {Target Commitment Evidence Verdict : Type u}
    (evaluate : Commitment → Evidence → Verdict)
    (old new : List (RoundRecord Target Commitment Evidence))
    (round : Nat)
    (appendOnly : AppendOnly old new)
    (oldRound : round < old.length) :
    settleAt evaluate new round = settleAt evaluate old round := by
  rcases appendOnly with ⟨tail, rfl⟩
  simp [settleAt, List.getElem?_append_left oldRound]

/-- A concrete nonempty old round and a distinct appended target version witness all
    hypotheses of the conservation theorem and a nontrivial settlement value. -/
example :
    ∃ evaluate : Nat → Nat → Nat,
      ∃ old tail : List (RoundRecord Bool Nat Nat),
        1 < old.length ∧
          AppendOnly old (old ++ tail) ∧
          settleAt evaluate (old ++ tail) 1 = some 7 ∧
          settleAt evaluate old 1 = some 7 := by
  let evaluate : Nat → Nat → Nat := fun commitment evidence => commitment + evidence
  let old : List (RoundRecord Bool Nat Nat) :=
    [ { target := false, commitment := 0, evidence := 0 },
      { target := false, commitment := 3, evidence := 4 } ]
  let tail : List (RoundRecord Bool Nat Nat) :=
    [ { target := true, commitment := 20, evidence := 30 } ]
  refine ⟨evaluate, old, tail, by simp [old], ?_, ?_, ?_⟩
  · exact ⟨tail, rfl⟩
  · simp [settleAt, evaluate, old, tail]
  · simp [settleAt, evaluate, old]

example :
    ∃ change : TargetChange Bool String String Nat Nat,
      VersionEdge (Reason := String) (Author := String) (Time := Nat) (Round := Nat)
        change.fromTarget change.toTarget := by
  let change : TargetChange Bool String String Nat Nat :=
    { fromTarget := false
      toTarget := true
      reason := "new evidence"
      author := "system"
      time := 1
      affectedRounds := {0} }
  exact ⟨change, target_change_is_version_edge change⟩

#print axioms append_only_old_settlement_unchanged

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
