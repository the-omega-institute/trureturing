/- GID: D5/S3/ConceptDynamics/ExperimentDesign/MinimumCompleteObserverSetCover
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/MinimumCompleteObserverSetCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Minimum-cost complete finite observer families are exactly minimum-cost set covers. -/

import D5.S3.ConceptDynamics.Experiment.FiniteExperimentCoverCriterion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-25):
   * Exact D5 hit `finite_experiment_cover_criterion` supplies the canonical
     joint-readout versus unordered-pair-cover equivalence and is applied
     directly for every candidate selection.
   * Current-tree searches for minimum-cost observers, weighted set cover,
     `argmin`, and cover-cost sums found no theorem packaging the optimization
     corollary. The adjacent CAS `finiteSelectionCost` uses a different carrier,
     so the source's cost sum is exposed directly rather than forked as a def.
   * Pinned Mathlib contains generic `Function.argminOn` and finite-sum APIs,
     but no theorem identifying these two source-constrained minimization
     problems. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.ExperimentDesign.MinimumCompleteObserverSetCover

open D5.S3.ConceptDynamics.Experiment.FiniteExperimentCoverCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open scoped BigOperators

universe u v

/-- A selected finite observer family has minimum total cost among complete
families exactly when it has minimum total cost among covers of the unordered
distinct-state-pair universe by the observers' separation sets. -/
theorem minimum_complete_observer_is_set_cover
    {n : Nat} {Observer : Type u} {Output : Observer -> Type v}
    (cost : Observer -> Real)
    (readout : (observer : Observer) -> Fin n -> Output observer)
    (selected : Finset Observer) :
    let identifies : Finset Observer -> Prop := fun selection =>
      Function.Injective
        (jointReadout
          (fun observer : {candidate // candidate ∈ selection} =>
            readout observer.1))
    let pairUniverse : Set (Sym2 (Fin n)) :=
      Sym2.fromRel (r := fun i j => i ≠ j)
        ⟨fun _ _ different => different.symm⟩
    let detector : Observer -> Set (Sym2 (Fin n)) := fun observer =>
      Sym2.fromRel
        (r := fun i j => i ≠ j ∧ readout observer i ≠ readout observer j)
        ⟨fun _ _ separated => ⟨separated.1.symm, separated.2.symm⟩⟩
    let covers : Finset Observer -> Prop := fun selection =>
      pairUniverse =
        ⋃ observer : {candidate // candidate ∈ selection}, detector observer.1
    let selectionCost : Finset Observer -> Real := fun selection =>
      ∑ observer ∈ selection, cost observer
    (identifies selected ∧
        ∀ candidate, identifies candidate ->
          selectionCost selected ≤ selectionCost candidate) ↔
      (covers selected ∧
        ∀ candidate, covers candidate ->
          selectionCost selected ≤ selectionCost candidate) := by
  dsimp only
  have coverCriterion (selection : Finset Observer) :
      Function.Injective
          (jointReadout
            (fun observer : {candidate // candidate ∈ selection} =>
              readout observer.1)) ↔
        Sym2.fromRel (r := fun i j : Fin n => i ≠ j)
            ⟨fun _ _ different => different.symm⟩ =
          ⋃ observer : {candidate // candidate ∈ selection},
            Sym2.fromRel
              (r := fun i j : Fin n =>
                i ≠ j ∧
                  readout observer.1 i ≠ readout observer.1 j)
              ⟨fun _ _ separated =>
                ⟨separated.1.symm, separated.2.symm⟩⟩ := by
    let rawUniverse : Set (Sym2 (Fin n)) :=
      Sym2.fromRel
        (r := fun i j : Fin n => (() : Unit) = () ∧ i ≠ j)
        ⟨fun _ _ unresolved => ⟨unresolved.1.symm, unresolved.2.symm⟩⟩
    let simpleUniverse : Set (Sym2 (Fin n)) :=
      Sym2.fromRel (r := fun i j : Fin n => i ≠ j)
        ⟨fun _ _ different => different.symm⟩
    let rawDetector (observer : Observer) : Set (Sym2 (Fin n)) :=
      Sym2.fromRel
        (r := fun i j : Fin n =>
          (() : Unit) = () ∧ i ≠ j ∧
            readout observer i ≠ readout observer j)
        ⟨fun _ _ separated =>
          ⟨separated.1.symm, separated.2.1.symm,
            separated.2.2.symm⟩⟩
    let simpleDetector (observer : Observer) : Set (Sym2 (Fin n)) :=
      Sym2.fromRel
        (r := fun i j : Fin n =>
          i ≠ j ∧ readout observer i ≠ readout observer j)
        ⟨fun _ _ separated =>
          ⟨separated.1.symm, separated.2.symm⟩⟩
    have universeEq : rawUniverse = simpleUniverse := by
      ext pair
      induction pair using Sym2.inductionOn with
      | _ i j =>
          change ((() : Unit) = () ∧ i ≠ j) ↔ i ≠ j
          simp
    have detectorEq (observer : Observer) :
        rawDetector observer = simpleDetector observer := by
      ext pair
      induction pair using Sym2.inductionOn with
      | _ i j =>
          change
            ((() : Unit) = () ∧ i ≠ j ∧
                readout observer i ≠ readout observer j) ↔
              (i ≠ j ∧ readout observer i ≠ readout observer j)
          simp
    have rawCriterion :
        (∀ i j,
            ((), jointReadout
                (fun observer : {candidate // candidate ∈ selection} =>
                  readout observer.1) i) =
              ((), jointReadout
                (fun observer : {candidate // candidate ∈ selection} =>
                  readout observer.1) j) ->
            i = j) ↔
          rawUniverse =
            ⋃ observer : {candidate // candidate ∈ selection},
              rawDetector observer.1 := by
      exact finite_experiment_cover_criterion selection
        (fun _ : Fin n => ()) readout (fun i => i)
    constructor
    · intro injective
      have rawCover := rawCriterion.mp
        (fun _ _ same => injective (congrArg Prod.snd same))
      have simpleCover :
          simpleUniverse =
            ⋃ observer : {candidate // candidate ∈ selection},
              simpleDetector observer.1 := by
        calc
          simpleUniverse = rawUniverse := universeEq.symm
          _ = ⋃ observer : {candidate // candidate ∈ selection},
              rawDetector observer.1 := rawCover
          _ = ⋃ observer : {candidate // candidate ∈ selection},
              simpleDetector observer.1 := by simp_rw [detectorEq]
      simpa [simpleUniverse, simpleDetector] using simpleCover
    · intro covers
      have simpleCover :
          simpleUniverse =
            ⋃ observer : {candidate // candidate ∈ selection},
              simpleDetector observer.1 := by
        simpa [simpleUniverse, simpleDetector] using covers
      have rawCover :
          rawUniverse =
            ⋃ observer : {candidate // candidate ∈ selection},
              rawDetector observer.1 := by
        calc
          rawUniverse = simpleUniverse := universeEq
          _ = ⋃ observer : {candidate // candidate ∈ selection},
              simpleDetector observer.1 := simpleCover
          _ = ⋃ observer : {candidate // candidate ∈ selection},
              rawDetector observer.1 := by simp_rw [detectorEq]
      have rawIdentifies := rawCriterion.mpr rawCover
      intro i j same
      exact rawIdentifies i j (Prod.ext rfl same)
  constructor
  · rintro ⟨identifiesSelected, minimumAmongIdentifying⟩
    refine ⟨(coverCriterion selected).mp identifiesSelected, ?_⟩
    intro candidate coversCandidate
    exact minimumAmongIdentifying candidate
      ((coverCriterion candidate).mpr coversCandidate)
  · rintro ⟨coversSelected, minimumAmongCovers⟩
    refine ⟨(coverCriterion selected).mpr coversSelected, ?_⟩
    intro candidate identifiesCandidate
    exact minimumAmongCovers candidate
      ((coverCriterion candidate).mp identifiesCandidate)

#print axioms minimum_complete_observer_is_set_cover

end D5.S3.ConceptDynamics.ExperimentDesign.MinimumCompleteObserverSetCover
