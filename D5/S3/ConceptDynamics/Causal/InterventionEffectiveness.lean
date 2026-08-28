/- GID: D5/S3/ConceptDynamics/Causal/InterventionEffectiveness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/InterventionEffectiveness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Intervened coordinates retain their assigned values in the final evaluation. -/

import D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics

/- Library-search audit trail (2026-08-26):
   * Exact repository hits `StructuralModel`, `intervenedEquation`, and
     `EvaluationWitness` provide the canonical structural-intervention semantics.
   * Exact pinned library hits `Function.update_self`, `Function.update_of_ne`,
     and `List.Nodup` provide the coordinate-preservation steps.
   * Repository searches for effectiveness, assigned intervention values, and
     final evaluation coordinates found no exact declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.InterventionEffectiveness

open D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics

private theorem evaluation_witness_preserves_coordinate
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U)
    {remaining : List (Fin n)} {state result : Fin n → X} {v : Fin n}
    (hv : v ∉ remaining)
    (hevaluation :
      EvaluationWitness model intervention assigned u remaining state result) :
    result v = state v := by
  induction remaining generalizing state with
  | nil =>
      simpa [EvaluationWitness] using congrFun hevaluation v
  | cons w remaining inductionHypothesis =>
      rcases hevaluation with ⟨_parentCondition, next, hnext, htail⟩
      subst next
      have hvw : v ≠ w := by
        intro hvw
        apply hv
        simp [hvw]
      have hvremaining : v ∉ remaining := by
        intro hmem
        exact hv (by simp [hmem])
      calc
        result v =
            (Function.update state w
              (intervenedEquation model intervention assigned w state u)) v :=
          inductionHypothesis hvremaining htail
        _ = state v := by simp [Function.update_of_ne, hvw]

private theorem evaluation_witness_intervention_value
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U)
    {remaining : List (Fin n)} {state result : Fin n → X} {v : Fin n}
    (hnodup : remaining.Nodup) (hvmem : v ∈ remaining)
    (hevaluation :
      EvaluationWitness model intervention assigned u remaining state result)
    (hv : v ∈ intervention) :
    result v = assigned v := by
  induction remaining generalizing state with
  | nil =>
      simp at hvmem
  | cons w remaining inductionHypothesis =>
      rcases List.nodup_cons.mp hnodup with ⟨hw, hremaining⟩
      rcases hevaluation with ⟨_parentCondition, next, hnext, htail⟩
      subst next
      by_cases hvw : v = w
      · subst w
        calc
          result v =
              (Function.update state v
                (intervenedEquation model intervention assigned v state u)) v :=
            evaluation_witness_preserves_coordinate
              model intervention assigned u hw htail
          _ = intervenedEquation model intervention assigned v state u := by
            simp only [Function.update_self]
          _ = assigned v := by simp [intervenedEquation, hv]
      · have hvmemaining : v ∈ remaining := by
          simpa [hvw] using hvmem
        exact inductionHypothesis hremaining hvmemaining htail

/-- In a completed structural evaluation, every coordinate selected by the
intervention has exactly the value assigned by that intervention. -/
theorem intervention_effectiveness
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U) (result : Fin n → X) (v : Fin n)
    (hevaluation :
      EvaluationWitness model intervention assigned u
        model.order (model.initial u) result)
    (hv : v ∈ intervention) :
    result v = assigned v := by
  exact evaluation_witness_intervention_value
    model intervention assigned u model.order_nodup
      (model.order_complete v) hevaluation hv

#print axioms intervention_effectiveness

end D5.S3.ConceptDynamics.Causal.InterventionEffectiveness
