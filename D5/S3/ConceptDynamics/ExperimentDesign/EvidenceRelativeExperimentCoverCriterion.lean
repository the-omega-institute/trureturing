/- GID: D5/S3/ConceptDynamics/ExperimentDesign/EvidenceRelativeExperimentCoverCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/EvidenceRelativeExperimentCoverCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evidence-relative target identification is ordered-pair cover. -/

import D5.S3.ConceptDynamics.Experiment.FiniteExperimentCoverCriterion

/- Library-search audit trail (2026-08-27):
   * `FiniteExperimentCoverCriterion.finite_experiment_cover_criterion` is the
     closest frozen family theorem, but it uses unordered `Sym2 (Fin n)` pairs.
     The source object below is the ordered carrier `Model × Model`, so that
     theorem is not an exact bind.
   * `TargetSufficiencyPairCover.target_sufficiency_iff_pair_cover` additionally
     omits the source's current-evidence interface and is not exact.
   * Exact family primitive `jointReadout` constructs the selected dependent
     experiment interface. No selected-readout or residual-pair definition is added.
   * Pinned Mathlib supplies `Function.FactorsThrough` and the Set union lemmas,
     but no evidence-relative ordered-pair cover criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentDesign.EvidenceRelativeExperimentCoverCriterion

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w x y

/-- A selected finite experiment family identifies a target relative to current
evidence exactly when it separates every ordered pair that current evidence
leaves unresolved and the target distinguishes. -/
theorem evidence_relative_experiment_cover_criterion
    {Model : Type u} {Experiment : Type v} {Evidence : Type w}
    {Response : Experiment -> Type x} {Target : Type y}
    (selected : Finset Experiment)
    (baseline : Model -> Evidence)
    (readout : (experiment : Experiment) -> Model -> Response experiment)
    (target : Model -> Target) :
    Function.FactorsThrough target
        (fun model =>
          (baseline model,
            jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                readout experiment.1) model)) ↔
      {pair : Model × Model |
          baseline pair.1 = baseline pair.2 ∧
            target pair.1 ≠ target pair.2} ⊆
        ⋃ experiment : {candidate // candidate ∈ selected},
          {pair : Model × Model |
            baseline pair.1 = baseline pair.2 ∧
              target pair.1 ≠ target pair.2 ∧
                readout experiment.1 pair.1 ≠ readout experiment.1 pair.2} := by
  classical
  constructor
  · intro identifies pair unresolved
    apply Set.mem_iUnion.mpr
    by_contra notCovered
    have sameSelectedReadout :
        jointReadout
            (fun experiment : {candidate // candidate ∈ selected} =>
              readout experiment.1) pair.1 =
          jointReadout
            (fun experiment : {candidate // candidate ∈ selected} =>
              readout experiment.1) pair.2 := by
      funext experiment
      by_contra separated
      apply notCovered
      refine ⟨experiment, ?_⟩
      exact ⟨unresolved.1, unresolved.2, separated⟩
    apply unresolved.2
    apply identifies
    exact Prod.ext unresolved.1 sameSelectedReadout
  · intro covers first second sameEvidence
    by_contra targetDifferent
    have unresolved :
        (first, second) ∈
          {pair : Model × Model |
            baseline pair.1 = baseline pair.2 ∧
              target pair.1 ≠ target pair.2} :=
      ⟨congrArg Prod.fst sameEvidence, targetDifferent⟩
    obtain ⟨experiment, separated⟩ := Set.mem_iUnion.mp (covers unresolved)
    apply separated.2.2
    exact congrFun (congrArg Prod.snd sameEvidence) experiment

#print axioms evidence_relative_experiment_cover_criterion

end D5.S3.ConceptDynamics.ExperimentDesign.EvidenceRelativeExperimentCoverCriterion
