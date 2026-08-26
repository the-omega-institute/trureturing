/- GID: D5/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A parent-ordered model has a unique post-intervention evaluation trace. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics

/- A finite structural model exposes its parent coordinates, equations, and
external-state initialization as separate source-semantic data. -/
structure StructuralModel (n : Nat) (X U : Type _) where
  order : List (Fin n)
  order_nodup : order.Nodup
  order_complete : ∀ v, v ∈ order
  parents : Fin n → Finset (Fin n)
  equation : (v : Fin n) → (parents v → X) → U → X
  initial : U → Fin n → X

/- A topological certificate states directly that no parent remains in the
tail when a node is reached in the supplied order. -/
def TopologicalOrder {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) : Prop :=
  ∀ (pre remaining : List (Fin n)) (v : Fin n),
    model.order = pre ++ v :: remaining →
      ∀ parent : model.parents v, parent.1 ∈ pre ∧ parent.1 ∉ remaining

def intervenedEquation {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (v : Fin n) (state : Fin n → X) (u : U) : X :=
  if v ∈ intervention then assigned v
  else model.equation v (fun parent => state parent.1) u

/- The trace records both the deterministic update and the fact that every
parent coordinate has already left the remaining topological tail. -/
def EvaluationWitness {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U) :
    List (Fin n) → (Fin n → X) → (Fin n → X) → Prop
  | [], state, result => result = state
  | v :: remaining, state, result =>
      (∀ parent : model.parents v, parent.1 ∉ remaining) ∧
        ∃ next : Fin n → X,
          next = Function.update state v
            (intervenedEquation model intervention assigned v state u) ∧
            EvaluationWitness model intervention assigned u remaining next result

private theorem evaluation_witness_unique
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (topological : TopologicalOrder model)
    (intervention : Finset (Fin n)) (assigned : Fin n → X) (u : U) :
    ∀ (remaining : List (Fin n)) (state : Fin n → X) (pre : List (Fin n)),
      model.order = pre ++ remaining →
        ∃! result : Fin n → X,
          EvaluationWitness model intervention assigned u remaining state result := by
  intro remaining
  induction remaining with
  | nil =>
      intro state pre horder
      refine ⟨state, rfl, ?_⟩
      intro result hresult
      exact hresult
  | cons v remaining inductionHypothesis =>
      intro state pre horder
      have parent_condition : ∀ parent : model.parents v, parent.1 ∉ remaining := by
        intro parent
        exact (topological pre remaining v
          (by simpa [List.append_assoc] using horder) parent).2
      let next : Fin n → X :=
        Function.update state v
          (intervenedEquation model intervention assigned v state u)
      obtain ⟨result, hresult, hunique⟩ :=
        inductionHypothesis next (pre ++ [v]) (by simpa [List.append_assoc] using horder)
      refine ⟨result, ?_, ?_⟩
      · exact ⟨parent_condition, next, rfl, hresult⟩
      · intro other hother
        rcases hother with ⟨_otherParentCondition, otherNext, hnext, htail⟩
        have hnext' : otherNext = next := hnext.trans rfl
        subst otherNext
        exact hunique other htail

/-- For every external state and intervention, a parent-indexed structural
model has a unique value assignment obtained by evaluating equations in its
certified topological order, with intervention values replacing equations. -/
theorem parent_ordered_structure_evaluation_semantics
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (topological : TopologicalOrder model)
    (intervention : Finset (Fin n)) (assigned : Fin n → X) (u : U) :
    ∃! result : Fin n → X,
      EvaluationWitness model intervention assigned u model.order (model.initial u) result := by
  exact evaluation_witness_unique model topological intervention assigned u
    model.order (model.initial u) [] (by simp)

#print axioms parent_ordered_structure_evaluation_semantics

end D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics
