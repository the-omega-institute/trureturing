/- GID: D5/S3/ConceptDynamics/Governance/CommitInterfaceSealPreservation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/CommitInterfaceSealPreservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Commit outputs seal coordinates and confine artifacts to the bundle and closure. -/

import D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/- Library-search audit trail (2026-08-28):
   * Exact search for `CommitInterface`, `candidateBundlePreserved`,
     `committedFromInput`, `CommitmentSeal`, `digestCovers`, and
     `sealedDependencyClosure` in `D5` and pinned Mathlib found no declaration.
   * Shape search for commitment seals, digest/closure preservation, candidate
     bundles, and commit interfaces found only the general ProspectiveCommitment
     carrier in TargetLaunderingCriterion. Its committedInClosure field is reused.
   * The source atom's CommitInterface and CommitmentSeal sketches therefore have
     no existing theorem to bind, while their commitment carrier is imported
     rather than duplicated. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.Governance.CommitInterfaceSealPreservation

open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/-- The finite artifact bundle supplied to one commit step. -/
structure CandidateBundle (Artifact : Type u) [DecidableEq Artifact] where
  artifacts : Finset Artifact

/-- A seal stores the digest and the three coordinates covered by that digest. -/
structure CommitmentSeal
    (Digest Commitment EventId Artifact : Type u)
    (digestOf : Commitment -> EventId -> Set Artifact -> Digest)
    (commitment : Commitment) (freezeEvent : EventId)
    (dependencyClosure : Set Artifact) where
  digest : Digest
  digestCovers : digest = digestOf commitment freezeEvent dependencyClosure
  sealedCommitment : Commitment
  sealsCommitment : sealedCommitment = commitment
  sealedFreezeEvent : EventId
  sealsFreezeEvent : sealedFreezeEvent = freezeEvent
  sealedDependencyClosure : Set Artifact
  sealsDependencyClosure : sealedDependencyClosure = dependencyClosure

/-- A commit interface returns a sealed prospective commitment and preserves the
input candidate bundle at both the decision and committed-artifact boundaries. -/
structure CommitInterface
    (RoundState Digest EventId Evidence Round Artifact Time TargetChain Domain
      Epsilon Condition Comparator TestPlan Baseline WeightSpec : Type u)
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    (n : Round) where
  defineStep : RoundState -> CandidateBundle Artifact
  digestOf :
    ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain Domain
      Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
      EventId -> Set Artifact -> Digest
  commitStep : (bundle : CandidateBundle Artifact) ->
    Sigma fun commitment :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n =>
      CommitmentSeal Digest
        (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
          Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
        EventId Artifact digestOf commitment
          commitment.adjudication.freezeEvent
          commitment.adjudication.dependencyClosure
  candidateBundlePreserved : forall bundle,
    (commitStep bundle).1.decision.candidates = bundle.artifacts
  committedFromInput : forall bundle,
    (commitStep bundle).1.committedArtifacts <= bundle.artifacts

/-- Every commit output has a digest over the complete commitment, freeze event,
and dependency closure. Its committed artifacts remain in the finite input bundle,
the sealed decision candidates, and the commitment's dependency closure. -/
theorem commit_interface_seal_and_artifact_preservation
    {RoundState Digest EventId Evidence Round Artifact Time TargetChain Domain
      Epsilon Condition Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (interface : CommitInterface RoundState Digest EventId Evidence Round Artifact
      Time TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (bundle : CandidateBundle Artifact) :
    let commitment := (interface.commitStep bundle).1
    let outputSeal := (interface.commitStep bundle).2
    outputSeal.digest = interface.digestOf commitment
        commitment.adjudication.freezeEvent
        commitment.adjudication.dependencyClosure ∧
      outputSeal.sealedCommitment = commitment ∧
      outputSeal.sealedFreezeEvent = commitment.adjudication.freezeEvent ∧
      outputSeal.sealedDependencyClosure =
        commitment.adjudication.dependencyClosure ∧
      commitment.decision.candidates = bundle.artifacts ∧
      forall artifact, artifact ∈ commitment.committedArtifacts ->
        artifact ∈ bundle.artifacts ∧
          artifact ∈ commitment.decision.candidates ∧
          artifact ∈ commitment.adjudication.dependencyClosure := by
  dsimp
  refine ⟨(interface.commitStep bundle).2.digestCovers,
    (interface.commitStep bundle).2.sealsCommitment,
    (interface.commitStep bundle).2.sealsFreezeEvent,
    (interface.commitStep bundle).2.sealsDependencyClosure,
    interface.candidateBundlePreserved bundle, ?_⟩
  intro artifact committed
  exact ⟨interface.committedFromInput bundle committed,
    (interface.commitStep bundle).1.committedFromCandidates committed,
    (interface.commitStep bundle).1.committedInClosure artifact committed⟩

namespace FiniteWitness

abbrev UnitCommitment :=
  ProspectiveCommitment Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit
    Unit ()

def filtration : EvidenceFiltration Unit Unit where
  seen := fun _ => Set.univ
  monotone := by simp

def snapshot : AdjudicationSnapshot Unit Unit Unit Unit Unit () where
  freezeEvent := ()
  decisionEvent := ()
  frozenAt := ()
  decidedAt := ()
  freezeBeforeDecision := le_rfl
  timeBeforeDecision := le_rfl
  filtration := filtration
  dependencyClosure := Set.univ
  evidenceDependencies := Set.univ

def commitment (bundle : CandidateBundle Unit) : UnitCommitment where
  adjudication := snapshot
  targetChain := ()
  domain := ()
  epsilon := ()
  conditions := ()
  comparator := ()
  testPlan := ()
  baseline := ()
  weightSpec := ()
  decision :=
    { candidates := bundle.artifacts
      feasible := bundle.artifacts
      current := none
      feasibleFromCandidates := by rfl }
  committedArtifacts := bundle.artifacts
  baselineArtifacts := bundle.artifacts
  committedFromCandidates := by rfl
  baselinesFromCandidates := by rfl
  committedInClosure := by simp [snapshot]

def digestOf : UnitCommitment -> Unit -> Set Unit -> Unit := fun _ _ _ => ()

def outputSeal (bundle : CandidateBundle Unit) :
    CommitmentSeal Unit UnitCommitment Unit Unit digestOf (commitment bundle)
      (commitment bundle).adjudication.freezeEvent
      (commitment bundle).adjudication.dependencyClosure where
  digest := ()
  digestCovers := rfl
  sealedCommitment := commitment bundle
  sealsCommitment := rfl
  sealedFreezeEvent := (commitment bundle).adjudication.freezeEvent
  sealsFreezeEvent := rfl
  sealedDependencyClosure := (commitment bundle).adjudication.dependencyClosure
  sealsDependencyClosure := rfl

def interface :
    CommitInterface Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit
      Unit Unit () where
  defineStep := fun _ => { artifacts := {()} }
  digestOf := digestOf
  commitStep := fun bundle => ⟨commitment bundle, outputSeal bundle⟩
  candidateBundlePreserved := by intro bundle; rfl
  committedFromInput := by intro bundle; rfl

def bundle : CandidateBundle Unit := { artifacts := {()} }

example : Nonempty (CandidateBundle Unit) := ⟨bundle⟩

example :
    Nonempty
      (CommitInterface Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit
        Unit Unit Unit ()) :=
  ⟨interface⟩

example :
    let commitment := (interface.commitStep bundle).1
    let outputSeal := (interface.commitStep bundle).2
    outputSeal.digest = interface.digestOf commitment
        commitment.adjudication.freezeEvent
        commitment.adjudication.dependencyClosure ∧
      outputSeal.sealedCommitment = commitment ∧
      outputSeal.sealedFreezeEvent = commitment.adjudication.freezeEvent ∧
      outputSeal.sealedDependencyClosure =
        commitment.adjudication.dependencyClosure ∧
      commitment.decision.candidates = bundle.artifacts ∧
      forall artifact, artifact ∈ commitment.committedArtifacts ->
        artifact ∈ bundle.artifacts ∧
          artifact ∈ commitment.decision.candidates ∧
          artifact ∈ commitment.adjudication.dependencyClosure :=
  commit_interface_seal_and_artifact_preservation interface bundle

end FiniteWitness

#print axioms commit_interface_seal_and_artifact_preservation

end D5.S3.ConceptDynamics.Governance.CommitInterfaceSealPreservation
