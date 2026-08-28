/- GID: D5/S3/ConceptDynamics/ExperimentDesign/TargetSufficiencyPairCover
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/TargetSufficiencyPairCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target sufficiency is exact coverage of target-disagreement pairs. -/

import D5.S3.ConceptDynamics.Experiment.FiniteExperimentCoverCriterion

/- Library-search audit trail (2026-08-27):
   * `FiniteExperimentCoverCriterion.finite_experiment_cover_criterion` is the
     closest family theorem, but its pair universe has an additional
     baseline-equality restriction. It is specialized to a constant `Unit`
     baseline below rather than duplicated.
   * `TargetRelativePairUniverse.target_relative_pair_universe` gives subset
     coverage by unrestricted separation sets, not equality with the source's
     target-restricted separation sets, so it is not an exact bind.
   * Exact primitives `jointReadout`, `Function.FactorsThrough`, and
     `Sym2.fromRel` construct the joint observation, target sufficiency, and
     unordered pair carrier. No sibling definitions are introduced.
   * Pinned Mathlib contains those primitives but no theorem combining them in
     this selected-family target-relative cover criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentDesign.TargetSufficiencyPairCover

open D5.S3.ConceptDynamics.Experiment.FiniteExperimentCoverCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- A finite selected experiment family determines a target exactly when the
union of its target-relevant separation sets is the full unordered universe of
target-disagreement pairs. -/
theorem target_sufficiency_iff_pair_cover
    {n : Nat} {Experiment : Type u} {Response : Experiment -> Type v}
    {Target : Type w} (selected : Finset Experiment)
    (readout : (experiment : Experiment) -> Fin n -> Response experiment)
    (target : Fin n -> Target) :
    Function.FactorsThrough target
        (jointReadout
          (fun experiment : {candidate // candidate ∈ selected} =>
            readout experiment.1)) ↔
      Sym2.fromRel (r := fun i j => target i ≠ target j)
          ⟨fun _ _ different => different.symm⟩ =
        ⋃ experiment : {candidate // candidate ∈ selected},
          Sym2.fromRel
            (r := fun i j =>
              target i ≠ target j ∧
                readout experiment.1 i ≠ readout experiment.1 j)
            ⟨fun _ _ separated =>
              ⟨separated.1.symm, separated.2.symm⟩⟩ := by
  let rawUniverse : Set (Sym2 (Fin n)) :=
    Sym2.fromRel
      (r := fun i j => (() : Unit) = () ∧ target i ≠ target j)
      ⟨fun _ _ unresolved => ⟨unresolved.1.symm, unresolved.2.symm⟩⟩
  let simpleUniverse : Set (Sym2 (Fin n)) :=
    Sym2.fromRel (r := fun i j => target i ≠ target j)
      ⟨fun _ _ different => different.symm⟩
  let rawDetector (experiment : Experiment) : Set (Sym2 (Fin n)) :=
    Sym2.fromRel
      (r := fun i j =>
        (() : Unit) = () ∧ target i ≠ target j ∧
          readout experiment i ≠ readout experiment j)
      ⟨fun _ _ separated =>
        ⟨separated.1.symm, separated.2.1.symm,
          separated.2.2.symm⟩⟩
  let simpleDetector (experiment : Experiment) : Set (Sym2 (Fin n)) :=
    Sym2.fromRel
      (r := fun i j =>
        target i ≠ target j ∧ readout experiment i ≠ readout experiment j)
      ⟨fun _ _ separated =>
        ⟨separated.1.symm, separated.2.symm⟩⟩
  have universeEq : rawUniverse = simpleUniverse := by
    ext pair
    induction pair using Sym2.inductionOn with
    | _ i j =>
        change (((() : Unit) = () ∧ target i ≠ target j) ↔
          target i ≠ target j)
        simp
  have detectorEq (experiment : Experiment) :
      rawDetector experiment = simpleDetector experiment := by
    ext pair
    induction pair using Sym2.inductionOn with
    | _ i j =>
        change (((() : Unit) = () ∧ target i ≠ target j ∧
            readout experiment i ≠ readout experiment j) ↔
          target i ≠ target j ∧
            readout experiment i ≠ readout experiment j)
        simp
  have rawCriterion :
      (∀ i j,
          ((), jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                readout experiment.1) i) =
            ((), jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                readout experiment.1) j) ->
          target i = target j) ↔
        rawUniverse =
          ⋃ experiment : {candidate // candidate ∈ selected},
            rawDetector experiment.1 := by
    exact finite_experiment_cover_criterion selected
      (fun _ : Fin n => ()) readout target
  constructor
  · intro sufficient
    have rawCovers := rawCriterion.mp (by
      intro i j sameCombined
      apply sufficient
      exact congrArg Prod.snd sameCombined)
    have simpleCovers :
        simpleUniverse =
          ⋃ experiment : {candidate // candidate ∈ selected},
            simpleDetector experiment.1 := by
      calc
        simpleUniverse = rawUniverse := universeEq.symm
        _ = ⋃ experiment : {candidate // candidate ∈ selected},
            rawDetector experiment.1 := rawCovers
        _ = ⋃ experiment : {candidate // candidate ∈ selected},
            simpleDetector experiment.1 := by simp_rw [detectorEq]
    simpa [simpleUniverse, simpleDetector] using simpleCovers
  · intro covers
    have simpleCovers :
        simpleUniverse =
          ⋃ experiment : {candidate // candidate ∈ selected},
            simpleDetector experiment.1 := by
      simpa [simpleUniverse, simpleDetector] using covers
    have rawCovers :
        rawUniverse =
          ⋃ experiment : {candidate // candidate ∈ selected},
            rawDetector experiment.1 := by
      calc
        rawUniverse = simpleUniverse := universeEq
        _ = ⋃ experiment : {candidate // candidate ∈ selected},
            simpleDetector experiment.1 := simpleCovers
        _ = ⋃ experiment : {candidate // candidate ∈ selected},
            rawDetector experiment.1 := by simp_rw [detectorEq]
    have rawSufficiency := rawCriterion.mpr rawCovers
    intro i j sameReadout
    apply rawSufficiency i j
    exact Prod.ext rfl sameReadout

#print axioms target_sufficiency_iff_pair_cover

end D5.S3.ConceptDynamics.ExperimentDesign.TargetSufficiencyPairCover
