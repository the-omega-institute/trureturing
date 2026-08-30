/- GID: D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Real-cost target minima equal weighted covers, with three degenerate witnesses. -/

import D5.S3.ConceptDynamics.ExperimentDesign.TargetSufficiencyPairCover
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-25):
   * Exact D5 hit `target_sufficiency_iff_pair_cover` supplies target feasibility.
   * `minimum_complete_observer_is_set_cover` has the required Real-cost shape,
     but its feasible designs identify every state rather than only the target.
   * Pinned-Mathlib searches found `Function.FactorsThrough`, `IsLeast`, and
     `Function.argminOn`, but no target-relative weighted-cover theorem or
     minimum-transport theorem. NyxID exposed no Loogle or LeanSearch service.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.ExperimentOptimization.MinimumCostTargetCover

open D5.S3.ConceptDynamics.ExperimentDesign.TargetSufficiencyPairCover
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open scoped BigOperators

universe u v w

/-- The unordered pairs of finite models on which the target values disagree. -/
def targetDisagreementPairs {n : Nat} {Target : Type w}
    (target : Fin n → Target) : Set (Sym2 (Fin n)) :=
  Sym2.fromRel (r := fun i j => target i ≠ target j)
    ⟨fun _ _ different => different.symm⟩

/-- The target-disagreement pairs separated by one intervention readout. -/
def interventionSeparationSet {n : Nat} {Intervention : Type u}
    {Response : Intervention → Type v} {Target : Type w}
    (readout : (intervention : Intervention) → Fin n → Response intervention)
    (target : Fin n → Target) (intervention : Intervention) :
    Set (Sym2 (Fin n)) :=
  Sym2.fromRel
    (r := fun i j =>
      target i ≠ target j ∧ readout intervention i ≠ readout intervention j)
    ⟨fun _ _ separated => ⟨separated.1.symm, separated.2.symm⟩⟩

/-- Minimum-cost target-sufficient designs are exactly minimum-cost covers of
the target-disagreement pairs. The cost is arbitrary: nonnegativity is not used
because the same objective is compared over equivalent feasible families. -/
theorem minimum_cost_target_sufficient_design_iff_pair_cover
    {n : Nat} {Intervention : Type u} {Response : Intervention → Type v}
    {Target : Type w} (cost : Intervention → Real)
    (readout : (intervention : Intervention) → Fin n → Response intervention)
    (target : Fin n → Target) (selected : Finset Intervention) :
    let sufficient : Finset Intervention → Prop := fun design =>
      Function.FactorsThrough target
        (jointReadout
          (fun intervention : {candidate // candidate ∈ design} =>
            readout intervention.1))
    let covers : Finset Intervention → Prop := fun design =>
      targetDisagreementPairs target =
        ⋃ intervention : {candidate // candidate ∈ design},
          interventionSeparationSet readout target intervention.1
    let designCost : Finset Intervention → Real := fun design =>
      ∑ intervention ∈ design, cost intervention
    (sufficient selected ∧
        ∀ candidate, sufficient candidate →
          designCost selected ≤ designCost candidate) ↔
      (covers selected ∧
        ∀ candidate, covers candidate →
          designCost selected ≤ designCost candidate) := by
  dsimp only
  have coverCriterion (design : Finset Intervention) :
      Function.FactorsThrough target
          (jointReadout
            (fun intervention : {candidate // candidate ∈ design} =>
              readout intervention.1)) ↔
        targetDisagreementPairs target =
          ⋃ intervention : {candidate // candidate ∈ design},
            interventionSeparationSet readout target intervention.1 := by
    simpa only [targetDisagreementPairs, interventionSeparationSet] using
      target_sufficiency_iff_pair_cover design readout target
  constructor
  · rintro ⟨sufficientSelected, minimumSufficient⟩
    refine ⟨(coverCriterion selected).mp sufficientSelected, ?_⟩
    intro candidate coversCandidate
    exact minimumSufficient candidate
      ((coverCriterion candidate).mpr coversCandidate)
  · rintro ⟨coversSelected, minimumCover⟩
    refine ⟨(coverCriterion selected).mpr coversSelected, ?_⟩
    intro candidate sufficientCandidate
    exact minimumCover candidate
      ((coverCriterion candidate).mp sufficientCandidate)

#print axioms minimum_cost_target_sufficient_design_iff_pair_cover

/-- With identically zero costs, every target-sufficient design is cost-minimal. -/
theorem zero_cost_target_sufficient_design_witness
    {n : Nat} {Intervention : Type u} {Response : Intervention → Type v}
    {Target : Type w}
    (readout : (intervention : Intervention) → Fin n → Response intervention)
    (target : Fin n → Target) (selected : Finset Intervention)
    (sufficient : Function.FactorsThrough target
      (jointReadout
        (fun intervention : {candidate // candidate ∈ selected} =>
          readout intervention.1))) :
    Function.FactorsThrough target
        (jointReadout
          (fun intervention : {candidate // candidate ∈ selected} =>
            readout intervention.1)) ∧
      ∀ candidate : Finset Intervention,
        (∑ _ ∈ selected, (0 : Real)) ≤
          ∑ _ ∈ candidate, (0 : Real) := by
  refine ⟨sufficient, ?_⟩
  intro candidate
  simp only [Finset.sum_const_zero]
  exact le_rfl

#print axioms zero_cost_target_sufficient_design_witness

/-- One identity intervention covers all target-disagreement pairs on `Fin 2`. -/
theorem singleton_intervention_cover_witness :
    let selected : Finset Unit := {()}
    let readout : Unit → Fin 2 → Fin 2 := fun _ => id
    let target : Fin 2 → Fin 2 := id
    Function.FactorsThrough target
        (jointReadout
          (fun intervention : {candidate // candidate ∈ selected} =>
            readout intervention.1)) ∧
      targetDisagreementPairs target =
        ⋃ intervention : {candidate // candidate ∈ selected},
          interventionSeparationSet readout target intervention.1 := by
  dsimp only
  have sufficient :
      Function.FactorsThrough (id : Fin 2 → Fin 2)
        (jointReadout
          (fun intervention : {candidate // candidate ∈ ({()} : Finset Unit)} =>
            (id : Fin 2 → Fin 2))) := by
    intro i j sameReadout
    exact congrFun sameReadout
      ⟨(), Finset.mem_singleton_self ()⟩
  refine ⟨sufficient, ?_⟩
  simpa only [targetDisagreementPairs, interventionSeparationSet] using
    (target_sufficiency_iff_pair_cover
      ({()} : Finset Unit) (fun _ : Unit => (id : Fin 2 → Fin 2))
      (id : Fin 2 → Fin 2)).mp sufficient

#print axioms singleton_intervention_cover_witness

/-- At horizon zero, the empty intervention type covers the constant target's
empty disagreement universe with the empty design. -/
theorem empty_target_cover_witness :
    let readout : (intervention : Empty) → Fin 0 → Unit :=
      Empty.elim
    let target : Fin 0 → Unit := fun _ => ()
    let selected : Finset Empty := ∅
    Function.FactorsThrough target
        (jointReadout
          (fun intervention : {candidate // candidate ∈ selected} =>
            readout intervention.1)) ∧
      targetDisagreementPairs target =
        ⋃ intervention : {candidate // candidate ∈ selected},
          interventionSeparationSet readout target intervention.1 := by
  dsimp only
  have sufficient :
      Function.FactorsThrough (fun _ : Fin 0 => ())
        (jointReadout
          (fun intervention : {candidate // candidate ∈ (∅ : Finset Empty)} =>
            (Empty.elim intervention.1 : Fin 0 → Unit))) := by
    intro i
    exact Fin.elim0 i
  refine ⟨sufficient, ?_⟩
  simpa only [targetDisagreementPairs, interventionSeparationSet] using
    (target_sufficiency_iff_pair_cover (∅ : Finset Empty)
      (fun intervention : Empty => (Empty.elim intervention : Fin 0 → Unit))
      (fun _ : Fin 0 => ())).mp sufficient

#print axioms empty_target_cover_witness

end D5.S3.ConceptDynamics.ExperimentOptimization.MinimumCostTargetCover
