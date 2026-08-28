/- GID: D5/S3/ConceptDynamics/Causal/RecursiveInterventionComposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/RecursiveInterventionComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A recursively realized node value makes its additional intervention redundant. -/

import D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics

/- Library-search audit trail (2026-08-26):
   * Repository searches for recursive intervention composition, redundant
     interventions, and an `EvaluationWitness` theorem involving `Finset.insert`
     found no exact declaration.
   * The frozen `ParentOrderedStructuralEvaluationSemantics` family supplies the
     canonical `StructuralModel`, `intervenedEquation`, and `EvaluationWitness`
     primitives; they are imported rather than redeclared.
   * Pinned Mathlib supplies the `Finset.insert` membership simplification and
     `Function.update` congruence used below, but no structural-model theorem of
     this shape. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.RecursiveInterventionComposition

open D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics

private theorem evaluation_witness_result_unique
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U) :
    ∀ {remaining : List (Fin n)} {state first second : Fin n → X},
      EvaluationWitness model intervention assigned u remaining state first →
      EvaluationWitness model intervention assigned u remaining state second →
      first = second := by
  intro remaining
  induction remaining with
  | nil =>
      intro state first second hfirst hsecond
      exact hfirst.trans hsecond.symm
  | cons v remaining inductionHypothesis =>
      intro state first second hfirst hsecond
      rcases hfirst with ⟨_firstParentCondition, firstNext, hfirstNext, hfirstTail⟩
      rcases hsecond with ⟨_secondParentCondition, secondNext, hsecondNext, hsecondTail⟩
      subst firstNext
      subst secondNext
      exact inductionHypothesis hfirstTail hsecondTail

private theorem evaluation_witness_preserves_absent_coordinate
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

private theorem evaluation_witness_insert_irrelevant
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U) (w : Fin n) :
    ∀ {remaining : List (Fin n)} {state result : Fin n → X},
      w ∉ remaining →
      (EvaluationWitness model intervention assigned u remaining state result ↔
        EvaluationWitness model (insert w intervention) assigned u
          remaining state result) := by
  intro remaining
  induction remaining with
  | nil =>
      intro state result _hw
      rfl
  | cons v remaining inductionHypothesis =>
      intro state result hw
      have hvw : v ≠ w := by
        intro hvw
        apply hw
        simp [hvw]
      have hwremaining : w ∉ remaining := by
        intro hmem
        exact hw (by simp [hmem])
      simp only [EvaluationWitness, intervenedEquation, Finset.mem_insert, hvw,
        false_or, inductionHypothesis hwremaining]

private theorem evaluation_witness_insert_redundant
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U) (w : Fin n) :
    ∀ {remaining : List (Fin n)} {state baseResult expandedResult : Fin n → X},
      remaining.Nodup →
      w ∈ remaining →
      EvaluationWitness model intervention assigned u
        remaining state baseResult →
      EvaluationWitness model (insert w intervention) assigned u
        remaining state expandedResult →
      baseResult w = assigned w →
      expandedResult = baseResult := by
  intro remaining
  induction remaining with
  | nil =>
      intro state baseResult expandedResult _hnodup hwmem
      simp at hwmem
  | cons v remaining inductionHypothesis =>
      intro state baseResult expandedResult hnodup hwmem hbase hexpanded hmatch
      rcases List.nodup_cons.mp hnodup with ⟨hvremaining, hremainingNodup⟩
      rcases hbase with ⟨_baseParentCondition, baseNext, hbaseNext, hbaseTail⟩
      rcases hexpanded with
        ⟨_expandedParentCondition, expandedNext, hexpandedNext, hexpandedTail⟩
      subst baseNext
      subst expandedNext
      by_cases hvw : v = w
      · subst v
        have hbaseAtW :
            baseResult w =
              intervenedEquation model intervention assigned w state u := by
          calc
            baseResult w =
                (Function.update state w
                  (intervenedEquation model intervention assigned w state u)) w :=
              evaluation_witness_preserves_absent_coordinate
                model intervention assigned u hvremaining hbaseTail
            _ = intervenedEquation model intervention assigned w state u := by simp
        have hequation :
            intervenedEquation model intervention assigned w state u = assigned w :=
          hbaseAtW.symm.trans hmatch
        have hexpandedAsBase :
            EvaluationWitness model intervention assigned u remaining
              (Function.update state w
                (intervenedEquation model intervention assigned w state u))
              expandedResult := by
          have hirrelevant :=
            (evaluation_witness_insert_irrelevant
              model intervention assigned u w hvremaining).mpr hexpandedTail
          rw [hequation]
          simpa [intervenedEquation] using hirrelevant
        exact evaluation_witness_result_unique
          model intervention assigned u hexpandedAsBase hbaseTail
      · have hwremaining : w ∈ remaining := by
          have hwv : w ≠ v := Ne.symm hvw
          simpa [hwv] using hwmem
        have hexpandedTail' :
            EvaluationWitness model (insert w intervention) assigned u remaining
              (Function.update state v
                (intervenedEquation model intervention assigned v state u))
              expandedResult := by
          simpa [intervenedEquation, hvw] using hexpandedTail
        exact inductionHypothesis hremainingNodup hwremaining
          hbaseTail hexpandedTail' hmatch

/-- If the evaluation under an intervention already realizes the value assigned
at `w`, additionally intervening at `w` leaves every downstream readout equal. -/
theorem recursive_intervention_composition
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U)
    (baseResult expandedResult : Fin n → X) (w y : Fin n)
    (hbase :
      EvaluationWitness model intervention assigned u
        model.order (model.initial u) baseResult)
    (hexpanded :
      EvaluationWitness model (insert w intervention) assigned u
        model.order (model.initial u) expandedResult)
    (hw : baseResult w = assigned w) :
    expandedResult y = baseResult y := by
  have hresults := evaluation_witness_insert_redundant
    model intervention assigned u w model.order_nodup
      (model.order_complete w) hbase hexpanded hw
  exact congrFun hresults y

#print axioms recursive_intervention_composition

end D5.S3.ConceptDynamics.Causal.RecursiveInterventionComposition
