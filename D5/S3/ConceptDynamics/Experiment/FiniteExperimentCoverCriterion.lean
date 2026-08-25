/- GID: D5/S3/ConceptDynamics/Experiment/FiniteExperimentCoverCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/FiniteExperimentCoverCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Selected experiments identify a target exactly by covering unresolved pairs. -/

import D5.S3.ConceptDynamics.Experiment.ExperimentIdentifiability
import D5.S3.ConceptDynamics.Interventions.TargetRelativePairUniverse

/- Library-search audit trail (2026-08-25):
   * `target_relative_pair_universe` and the cover conjunct of
     `target_pair_coverage_and_information_contrast` cover every target-distinct
     pair but omit the current evidence interface, so neither is an exact bind.
   * Exact family primitive `jointReadout` constructs the selected experiment
     package below; no selected-readout sibling definition is introduced.
   * Exact pinned-Mathlib hit `Sym2.fromRel` supplies the canonical unordered
     pair carrier. Repository body-shape searches found no theorem equating the
     current-evidence unresolved pairs with the selected separation union. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Experiment.FiniteExperimentCoverCriterion

open D5.S3.ConceptDynamics.Experiment.ExperimentIdentifiability
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- A finite selected experiment package identifies the target relative to the
current evidence exactly when its separation sets cover every unordered pair
that the current evidence leaves unresolved but the target distinguishes. -/
theorem finite_experiment_cover_criterion
    {n : Nat} {Experiment : Type u} {Evidence : Type v}
    {Response : Experiment -> Type w} {Target : Type z}
    (selected : Finset Experiment)
    (baseline : Fin n -> Evidence)
    (readout : (experiment : Experiment) -> Fin n -> Response experiment)
    (target : Fin n -> Target) :
    (∀ i j,
        (baseline i,
            jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                readout experiment.1) i) =
          (baseline j,
            jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                readout experiment.1) j) ->
        target i = target j) ↔
      Sym2.fromRel
          (r := fun i j => baseline i = baseline j ∧ target i ≠ target j)
          ⟨fun _ _ unresolved => ⟨unresolved.1.symm, unresolved.2.symm⟩⟩ =
        ⋃ experiment : {candidate // candidate ∈ selected},
          Sym2.fromRel
            (r := fun i j =>
              baseline i = baseline j ∧
                target i ≠ target j ∧
                readout experiment.1 i ≠ readout experiment.1 j)
            ⟨fun _ _ separated =>
              ⟨separated.1.symm, separated.2.1.symm,
                separated.2.2.symm⟩⟩ := by
  classical
  constructor
  · intro identifies
    apply Set.Subset.antisymm
    · intro pair unresolved
      induction pair using Sym2.inductionOn with
      | _ i j =>
          change baseline i = baseline j ∧ target i ≠ target j at unresolved
          apply Set.mem_iUnion.mpr
          by_contra notCovered
          have sameSelectedReadout :
              ∀ experiment : {candidate // candidate ∈ selected},
                readout experiment.1 i = readout experiment.1 j := by
            intro experiment
            by_contra separated
            apply notCovered
            refine ⟨experiment, ?_⟩
            change baseline i = baseline j ∧
              target i ≠ target j ∧
              readout experiment.1 i ≠ readout experiment.1 j
            exact ⟨unresolved.1, unresolved.2, separated⟩
          have sameEvidence :
              (baseline i,
                  jointReadout
                    (fun experiment : {candidate // candidate ∈ selected} =>
                      readout experiment.1) i) =
                (baseline j,
                  jointReadout
                    (fun experiment : {candidate // candidate ∈ selected} =>
                      readout experiment.1) j) := by
            apply Prod.ext
            · exact unresolved.1
            · funext experiment
              exact sameSelectedReadout experiment
          exact unresolved.2 (identifies i j sameEvidence)
    · intro pair covered
      obtain ⟨experiment, separated⟩ := Set.mem_iUnion.mp covered
      induction pair using Sym2.inductionOn with
      | _ i j =>
          change baseline i = baseline j ∧
            target i ≠ target j ∧
            readout experiment.1 i ≠ readout experiment.1 j at separated
          change baseline i = baseline j ∧ target i ≠ target j
          exact ⟨separated.1, separated.2.1⟩
  · intro covers i j sameEvidence
    by_contra targetDifferent
    have unresolved :
        s(i, j) ∈ Sym2.fromRel
          (r := fun x y => baseline x = baseline y ∧ target x ≠ target y)
          ⟨fun _ _ pair => ⟨pair.1.symm, pair.2.symm⟩⟩ := by
      change baseline i = baseline j ∧ target i ≠ target j
      exact ⟨congrArg Prod.fst sameEvidence, targetDifferent⟩
    have covered :
        s(i, j) ∈
          ⋃ experiment : {candidate // candidate ∈ selected},
            Sym2.fromRel
              (r := fun x y =>
                baseline x = baseline y ∧
                  target x ≠ target y ∧
                  readout experiment.1 x ≠ readout experiment.1 y)
              ⟨fun _ _ separated =>
                ⟨separated.1.symm, separated.2.1.symm,
                  separated.2.2.symm⟩⟩ := by
      rw [← covers]
      exact unresolved
    obtain ⟨experiment, separated⟩ := Set.mem_iUnion.mp covered
    change baseline i = baseline j ∧
      target i ≠ target j ∧
      readout experiment.1 i ≠ readout experiment.1 j at separated
    have sameJointReadout := congrArg Prod.snd sameEvidence
    exact separated.2.2 (congrFun sameJointReadout experiment)

#print axioms finite_experiment_cover_criterion

end D5.S3.ConceptDynamics.Experiment.FiniteExperimentCoverCriterion
