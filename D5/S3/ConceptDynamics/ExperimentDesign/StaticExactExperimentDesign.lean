/- GID: D5/S3/ConceptDynamics/ExperimentDesign/StaticExactExperimentDesign
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/StaticExactExperimentDesign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two complementary change experiments are jointly exact, and every exact static selection contains both. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Tactic

/- Library-search audit trail (2026-08-26):
   * Exact current-tree searches for static exact experiment designs and the
     concrete three-model response table found no deposited theorem.
   * Exact current-tree hit `jointReadout` is the canonical dependent product
     of experiment responses and is imported rather than redeclared.
   * Pinned-Mathlib searches for paired injectivity and finite Boolean
     selections found generic injectivity and finset APIs, but no theorem
     packaging this response table and its minimum exact selection. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- In the three-model change-response table, either experiment alone identifies
at most two classes, the two experiments together identify every model, and any
static exact experiment selection must contain both experiment roles. -/
theorem static_exact_design :
    let changeX : Fin 3 -> Bool := fun model => decide (model = 1)
    let changeY : Fin 3 -> Bool := fun model => decide (model = 2)
    (forall experiment : Bool,
        Not (Function.Injective
          (fun model => if experiment then changeY model else changeX model))) ∧
      Function.Injective
        (jointReadout
          (fun experiment : Bool =>
            if experiment then changeY else changeX)) ∧
      forall selected : Finset Bool,
        Function.Injective
            (jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                if experiment.1 then changeY else changeX)) ->
          selected = {false, true} := by
  dsimp only
  constructor
  · intro experiment
    cases experiment with
    | false =>
        intro injective
        have collision : (0 : Fin 3) = 2 := injective (by decide)
        omega
    | true =>
        intro injective
        have collision : (0 : Fin 3) = 1 := injective (by decide)
        omega
  constructor
  · intro left right sameReadout
    have sameChangeX := congrFun sameReadout false
    have sameChangeY := congrFun sameReadout true
    fin_cases left <;> fin_cases right <;>
      simp_all [jointReadout]
  · intro selected injective
    have hasChangeX : false ∈ selected := by
      by_contra absent
      have sameReadout :
          jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                if experiment.1 then
                  (fun model : Fin 3 => decide (model = 2))
                else
                  (fun model : Fin 3 => decide (model = 1)))
              (0 : Fin 3) =
            jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                if experiment.1 then
                  (fun model : Fin 3 => decide (model = 2))
                else
                  (fun model : Fin 3 => decide (model = 1)))
              (1 : Fin 3) := by
        funext experiment
        have isChangeY : experiment.1 = true := by
          apply Bool.eq_true_of_not_eq_false
          intro isChangeX
          apply absent
          simpa [isChangeX] using experiment.2
        simp [jointReadout, isChangeY]
      have collision : (0 : Fin 3) = 1 := injective sameReadout
      omega
    have hasChangeY : true ∈ selected := by
      by_contra absent
      have sameReadout :
          jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                if experiment.1 then
                  (fun model : Fin 3 => decide (model = 2))
                else
                  (fun model : Fin 3 => decide (model = 1)))
              (0 : Fin 3) =
            jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                if experiment.1 then
                  (fun model : Fin 3 => decide (model = 2))
                else
                  (fun model : Fin 3 => decide (model = 1)))
              (2 : Fin 3) := by
        funext experiment
        have isChangeX : experiment.1 = false := by
          apply Bool.eq_false_of_not_eq_true
          intro isChangeY
          apply absent
          simpa [isChangeY] using experiment.2
        simp [jointReadout, isChangeX]
      have collision : (0 : Fin 3) = 2 := injective sameReadout
      omega
    ext experiment
    cases experiment <;> simp [hasChangeX, hasChangeY]

#print axioms static_exact_design

end D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
