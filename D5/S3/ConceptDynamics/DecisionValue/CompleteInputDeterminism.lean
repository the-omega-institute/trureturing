/- GID: D5/S3/ConceptDynamics/DecisionValue/CompleteInputDeterminism
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/CompleteInputDeterminism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic disagreement exposes a difference in at least one complete input. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Logic.Relator

/- Library-search audit trail (2026-08-21):
   * Repository searches for complete decision inputs, deterministic disagreement,
     input-layer differences, and the eight source components found no exact theorem.
   * `CommonRuleInformationConvergence` is adjacent but strictly narrower: it
     compares correct fact values under one rule rather than all decision inputs.
   * Exact pinned-Mathlib hit `Relator.RightUnique` expresses deterministic
     relational output and is used directly as the public determinism hypothesis.
   * No pinned theorem packages its eight-field contrapositive. The `loogle` and
     `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.CompleteInputDeterminism

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- All source-level inputs presented to a decision relation: an evidence
channel and value, admission predicate, inference relation, value channel,
available actions, random seed, and actual anchor. -/
structure CompleteDecisionInput
    (World Evidence Claim Action Value Seed : Type*) where
  evidenceConcept : Concept World Evidence
  evidenceValue : Evidence
  admissionDomain : Set World
  inferenceRule : Evidence -> Claim -> Prop
  valueDoctrine : Action -> Value
  actionSet : Set Action
  randomSeed : Seed
  actualAnchor : World

/-- A right-unique decision relation agrees on completely identical inputs;
conversely, unequal related decisions expose a difference in at least one of
the eight public input components. -/
theorem complete_input_agreement_excludes_deterministic_disagreement
    {World Evidence Claim Action Value Seed : Type*}
    (decisioner :
      CompleteDecisionInput World Evidence Claim Action Value Seed ->
        Action -> Prop)
    (deterministic : Relator.RightUnique decisioner)
    (leftEvidenceConcept rightEvidenceConcept : Concept World Evidence)
    (leftEvidenceValue rightEvidenceValue : Evidence)
    (leftAdmissionDomain rightAdmissionDomain : Set World)
    (leftInferenceRule rightInferenceRule : Evidence -> Claim -> Prop)
    (leftValueDoctrine rightValueDoctrine : Action -> Value)
    (leftActionSet rightActionSet : Set Action)
    (leftRandomSeed rightRandomSeed : Seed)
    (leftActualAnchor rightActualAnchor : World)
    (leftDecision rightDecision : Action)
    (leftRelated : decisioner
      ⟨leftEvidenceConcept, leftEvidenceValue, leftAdmissionDomain,
        leftInferenceRule, leftValueDoctrine, leftActionSet, leftRandomSeed,
        leftActualAnchor⟩ leftDecision)
    (rightRelated : decisioner
      ⟨rightEvidenceConcept, rightEvidenceValue, rightAdmissionDomain,
        rightInferenceRule, rightValueDoctrine, rightActionSet, rightRandomSeed,
        rightActualAnchor⟩ rightDecision) :
    ((leftEvidenceConcept = rightEvidenceConcept ∧
      leftEvidenceValue = rightEvidenceValue ∧
      leftAdmissionDomain = rightAdmissionDomain ∧
      leftInferenceRule = rightInferenceRule ∧
      leftValueDoctrine = rightValueDoctrine ∧
      leftActionSet = rightActionSet ∧
      leftRandomSeed = rightRandomSeed ∧
      leftActualAnchor = rightActualAnchor) ->
        leftDecision = rightDecision) ∧
    (leftDecision ≠ rightDecision ->
      leftEvidenceConcept ≠ rightEvidenceConcept ∨
      leftEvidenceValue ≠ rightEvidenceValue ∨
      leftAdmissionDomain ≠ rightAdmissionDomain ∨
      leftInferenceRule ≠ rightInferenceRule ∨
      leftValueDoctrine ≠ rightValueDoctrine ∨
      leftActionSet ≠ rightActionSet ∨
      leftRandomSeed ≠ rightRandomSeed ∨
      leftActualAnchor ≠ rightActualAnchor) := by
  have agreement :
      (leftEvidenceConcept = rightEvidenceConcept ∧
        leftEvidenceValue = rightEvidenceValue ∧
        leftAdmissionDomain = rightAdmissionDomain ∧
        leftInferenceRule = rightInferenceRule ∧
        leftValueDoctrine = rightValueDoctrine ∧
        leftActionSet = rightActionSet ∧
        leftRandomSeed = rightRandomSeed ∧
        leftActualAnchor = rightActualAnchor) ->
      leftDecision = rightDecision := by
    rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact deterministic leftRelated rightRelated
  refine ⟨agreement, ?_⟩
  intro decisionsDiffer
  by_contra noInputDiffers
  simp only [not_or, not_ne_iff] at noInputDiffers
  exact decisionsDiffer (agreement noInputDiffers)

/-- The complete input carrier is inhabited by concrete source primitives. -/
example : CompleteDecisionInput Bool Bool Bool Bool Nat Bool :=
  ⟨id, true, Set.univ, (fun evidence claim => evidence = claim),
    (fun action => if action then 1 else 0), Set.univ, false, true⟩

/-- The public relation and determinism hypotheses have a concrete model. -/
example :
    let input : CompleteDecisionInput Bool Bool Bool Bool Nat Bool :=
      ⟨id, true, Set.univ, (fun evidence claim => evidence = claim),
        (fun action => if action then 1 else 0), Set.univ, false, true⟩
    let decisioner := fun observed output => observed = input ∧ output = true
    Relator.RightUnique decisioner ∧ decisioner input true := by
  dsimp
  constructor
  · intro _ leftOutput rightOutput leftRelated rightRelated
    exact leftRelated.2.trans rightRelated.2.symm
  · exact ⟨rfl, rfl⟩

/-- Without right uniqueness, one completely identical input can have unequal
related decisions, falsifying both conclusions when detached from determinism. -/
example :
    let input : CompleteDecisionInput Bool Bool Bool Bool Nat Bool :=
      ⟨id, true, Set.univ, (fun evidence claim => evidence = claim),
        (fun action => if action then 1 else 0), Set.univ, false, true⟩
    let nondeterministic := fun observed (_ : Bool) => observed = input
    nondeterministic input false ∧ nondeterministic input true ∧ false ≠ true := by
  exact ⟨rfl, rfl, Bool.false_ne_true⟩

#print axioms complete_input_agreement_excludes_deterministic_disagreement

end D5.S3.ConceptDynamics.DecisionValue.CompleteInputDeterminism
