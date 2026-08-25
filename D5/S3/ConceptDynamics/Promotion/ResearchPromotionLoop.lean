/- GID: D5/S3/ConceptDynamics/Promotion/ResearchPromotionLoop
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Promotion/ResearchPromotionLoop
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ledgers prune; walls persist; release forces escape; promotion receipts are typed. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold

/- Library-search audit trail (2026-08-24):
   * `rg -n 'Survives|survivors_antitone|ClassWall|PromotionChain|
     released_anchor_has_receipt' D5 --glob '*.lean'` found no repository hit.
   * Pinned Mathlib searches for `Finset.mem_filter`,
     `Finset.filter_eq_empty_iff`, and `all_eq_true` found generic filter
     support but no `Finset.all`; a later `Finset.fold` search found the
     commutative fold characterization used below.
   * `Statement → False` would refute the whole statement-code carrier, not one
     selected code. The verdict below instead stores proof or refutation data
     indexed by explicit `certifies` and `refutes` evidence relations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Promotion.ResearchPromotionLoop

universe uCandidate uFalsifier uStatement uProof uNode uAnchor uSeed

/-- A candidate survives when no falsifier in the ledger kills it. -/
def Survives
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    (ledger : Finset Falsifier) (kills : Falsifier → Candidate → Bool)
    (candidate : Candidate) : Prop :=
  ∀ falsifier ∈ ledger, kills falsifier candidate = false

/-- A commutative Boolean fold tests whether every ledger entry spares a candidate. -/
def survivesBool
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    (ledger : Finset Falsifier) (kills : Falsifier → Candidate → Bool)
    (candidate : Candidate) : Bool :=
  Finset.fold (fun left right => left && right) true
    (fun falsifier => !kills falsifier candidate) ledger

/-- The Boolean ledger fold reflects propositional survival. -/
theorem survivesBool_eq_true_iff
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    (ledger : Finset Falsifier) (kills : Falsifier → Candidate → Bool)
    (candidate : Candidate) :
    survivesBool ledger kills candidate = true ↔
      Survives ledger kills candidate := by
  unfold survivesBool Survives
  have foldCharacterization :=
    Finset.fold_op_rel_iff_and
      (op := fun left right : Bool => left && right)
      (r := fun _ actual : Bool => actual = true)
      (b := true) (f := fun falsifier => !kills falsifier candidate)
      (s := ledger) (c := true) (by
        intro expected left right
        simp)
  simpa using foldCharacterization

/-- The surviving part of a finite candidate pool. -/
def survivors
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    [DecidableEq Candidate]
    (pool : Finset Candidate) (ledger : Finset Falsifier)
    (kills : Falsifier → Candidate → Bool) : Finset Candidate :=
  pool.filter (fun candidate => survivesBool ledger kills candidate)

/-- Filter membership is exactly pool membership plus ledger survival. -/
theorem mem_survivors_iff
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    [DecidableEq Candidate]
    (pool : Finset Candidate) (ledger : Finset Falsifier)
    (kills : Falsifier → Candidate → Bool) (candidate : Candidate) :
    candidate ∈ survivors pool ledger kills ↔
      candidate ∈ pool ∧ Survives ledger kills candidate := by
  simp [survivors, survivesBool_eq_true_iff]

/-- Ledger growth can only remove candidates from a fixed pool. -/
theorem survivors_antitone
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    [DecidableEq Candidate]
    (pool : Finset Candidate) {ledger ledger' : Finset Falsifier}
    (kills : Falsifier → Candidate → Bool) (growth : ledger ⊆ ledger') :
    survivors pool ledger' kills ⊆ survivors pool ledger kills := by
  intro candidate inLargerLedger
  rw [mem_survivors_iff] at inLargerLedger ⊢
  refine ⟨inLargerLedger.1, ?_⟩
  intro falsifier inLedger
  exact inLargerLedger.2 falsifier (growth inLedger)

/-- A class wall says every class member is killed by the current ledger. -/
def ClassWall
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    (cls : Finset Candidate) (ledger : Finset Falsifier)
    (kills : Falsifier → Candidate → Bool) : Prop :=
  ∀ candidate ∈ cls, ¬Survives ledger kills candidate

/-- A wall remains valid after the falsifier ledger grows. -/
theorem classWall_stable
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    (cls : Finset Candidate) {ledger ledger' : Finset Falsifier}
    (kills : Falsifier → Candidate → Bool)
    (wall : ClassWall cls ledger kills) (growth : ledger ⊆ ledger') :
    ClassWall cls ledger' kills := by
  intro candidate inClass survivesLarger
  apply wall candidate inClass
  intro falsifier inLedger
  exact survivesLarger falsifier (growth inLedger)

/-- A candidate released alive past a wall cannot belong to the walled class. -/
theorem release_requires_escape
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    (cls : Finset Candidate) (ledger : Finset Falsifier)
    (kills : Falsifier → Candidate → Bool) (candidate : Candidate)
    (wall : ClassWall cls ledger kills)
    (alive : Survives ledger kills candidate) :
    candidate ∉ cls := by
  intro inClass
  exact wall candidate inClass alive

/-- A finite class is walled exactly when it has no surviving member. -/
theorem classWall_iff_survivors_empty
    {Candidate : Type uCandidate} {Falsifier : Type uFalsifier}
    [DecidableEq Candidate]
    (cls : Finset Candidate) (ledger : Finset Falsifier)
    (kills : Falsifier → Candidate → Bool) :
    ClassWall cls ledger kills ↔ survivors cls ledger kills = ∅ := by
  constructor
  · intro wall
    apply Finset.eq_empty_iff_forall_notMem.2
    intro candidate inSurvivors
    have memberData :=
      (mem_survivors_iff cls ledger kills candidate).1 inSurvivors
    exact wall candidate memberData.1 memberData.2
  · intro emptySurvivors candidate inClass survivesCandidate
    have inSurvivors :=
      (mem_survivors_iff cls ledger kills candidate).2
        ⟨inClass, survivesCandidate⟩
    rw [emptySurvivors] at inSurvivors
    simp at inSurvivors

/-- A proof receipt is evidence tied to one exact statement code. -/
structure ProofReceipt
    {Statement : Type uStatement} {Proof : Type uProof}
    (certifies : Proof → Statement → Prop) (statement : Statement) where
  proof : Proof
  evidence : certifies proof statement

/-- A refutation receipt is evidence tied to one exact statement code. -/
structure RefutationReceipt
    {Statement : Type uStatement} {Proof : Type uProof}
    (refutes : Proof → Statement → Prop) (statement : Statement) where
  proof : Proof
  evidence : refutes proof statement

/-- A typed verdict carries evidence for the selected statement in either direction. -/
inductive PromotionVerdict
    {Statement : Type uStatement} {Proof : Type uProof}
    (certifies refutes : Proof → Statement → Prop)
    (statement : Statement) where
  | proved (receipt : ProofReceipt certifies statement)
  | refuted (receipt : RefutationReceipt refutes statement)

/-- Only a proved verdict authorizes release. -/
def PromotionVerdict.IsReleased
    {Statement : Type uStatement} {Proof : Type uProof}
    {certifies refutes : Proof → Statement → Prop} {statement : Statement} :
    PromotionVerdict certifies refutes statement → Prop
  | .proved _ => True
  | .refuted _ => False

/-- Typed bookkeeping from proposal through verdict, frozen node, anchor, and seed. -/
structure PromotionChain
    (Candidate : Type uCandidate) (Statement : Type uStatement)
    (Proof : Type uProof) (Node : Type uNode) (Anchor : Type uAnchor)
    (Seed : Type uSeed) where
  proposal : Candidate
  exactStatement : Statement
  statementOf : Candidate → Statement
  statement_faithful : exactStatement = statementOf proposal
  certifies : Proof → Statement → Prop
  refutes : Proof → Statement → Prop
  verdict : PromotionVerdict certifies refutes exactStatement
  released : PromotionVerdict.IsReleased verdict
  nodeOf : PromotionVerdict certifies refutes exactStatement → Node
  frozenNode : Node
  node_faithful : frozenNode = nodeOf verdict
  anchorOf : Node → Anchor
  releasedAnchor : Anchor
  anchor_faithful : releasedAnchor = anchorOf frozenNode
  seedOf : Anchor → Seed
  researchSeed : Seed
  seed_faithful : researchSeed = seedOf releasedAnchor

/-- Every released anchor projects a proof receipt and the complete typed link chain. -/
theorem released_anchor_has_receipt
    {Candidate : Type uCandidate} {Statement : Type uStatement}
    {Proof : Type uProof} {Node : Type uNode} {Anchor : Type uAnchor}
    {Seed : Type uSeed}
    (chain : PromotionChain Candidate Statement Proof Node Anchor Seed) :
    ∃ receipt : ProofReceipt chain.certifies chain.exactStatement,
      chain.verdict = PromotionVerdict.proved receipt ∧
        chain.exactStatement = chain.statementOf chain.proposal ∧
        chain.frozenNode = chain.nodeOf chain.verdict ∧
        chain.releasedAnchor = chain.anchorOf chain.frozenNode ∧
        chain.researchSeed = chain.seedOf chain.releasedAnchor := by
  cases verdictEquation : chain.verdict with
  | proved receipt =>
      refine ⟨receipt, rfl, chain.statement_faithful, ?_,
        chain.anchor_faithful, chain.seed_faithful⟩
      simpa [verdictEquation] using chain.node_faithful
  | refuted receipt =>
      have impossible : False := by
        have released := chain.released
        rw [verdictEquation] at released
        exact released
      exact impossible.elim

#print axioms mem_survivors_iff
#print axioms survivesBool_eq_true_iff
#print axioms survivors_antitone
#print axioms classWall_stable
#print axioms release_requires_escape
#print axioms classWall_iff_survivors_empty
#print axioms released_anchor_has_receipt

end D5.S3.ConceptDynamics.Promotion.ResearchPromotionLoop
