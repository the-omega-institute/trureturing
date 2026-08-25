/- GID: D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite parent-ordered model has a unique post-intervention evaluation trace. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.StructuralEvaluationSemantics

/- A source-level finite structural model: nodes have parent relations, equations,
and an external-state initialization. The order is supplied separately with its
topological certificate, so the graph data is not hidden in the conclusion. -/
structure StructuralModel (n : Nat) (X U : Type _) where
  order : List (Fin n)
  order_nodup : order.Nodup
  order_complete : ∀ v, v ∈ order
  parents : Fin n → Finset (Fin n)
  equation : Fin n → (Fin n → X) → U → X
  initial : U → Fin n → X

def Before {n : Nat} (order : List (Fin n)) (a b : Fin n) : Prop :=
  ∃ left middle right : List (Fin n),
    order = left ++ [a] ++ middle ++ [b] ++ right

def TopologicalOrder {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) : Prop :=
  ∀ ⦃parent child⦄, parent ∈ model.parents child -> Before model.order parent child

def intervenedEquation {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (v : Fin n) (state : Fin n → X) (u : U) : X :=
  if v ∈ intervention then assigned v else model.equation v state u

def EvaluationWitness {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U) :
    List (Fin n) → (Fin n → X) → (Fin n → X) → Prop
  | [], state, result => result = state
  | v :: remaining, state, result =>
      ∃ next : Fin n → X,
        next = Function.update state v (intervenedEquation model intervention assigned v state u) ∧
          EvaluationWitness model intervention assigned u remaining next result

private theorem evaluation_witness_unique
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (intervention : Finset (Fin n))
    (assigned : Fin n → X) (u : U) :
    ∀ (remaining : List (Fin n)) (state : Fin n → X),
      ∃! result : Fin n → X,
        EvaluationWitness model intervention assigned u remaining state result := by
  intro remaining
  induction remaining with
  | nil =>
      intro state
      refine ⟨state, rfl, ?_⟩
      intro result hresult
      exact hresult
  | cons v remaining inductionHypothesis =>
      intro state
      let next : Fin n → X :=
        Function.update state v (intervenedEquation model intervention assigned v state u)
      obtain ⟨result, hresult, hunique⟩ := inductionHypothesis next
      refine ⟨result, ?_, ?_⟩
      · exact ⟨next, rfl, hresult⟩
      · intro other hother
        rcases hother with ⟨otherNext, hnext, htail⟩
        have hnext' : otherNext = next := hnext.trans rfl
        subst otherNext
        exact hunique other htail

/-- For every external state and intervention, the post-intervention system has
a unique value assignment obtained by evaluating equations in its certified DAG
topological order. -/
theorem structure_evaluation_semantics
    {n : Nat} {X U : Type _}
    (model : StructuralModel n X U) (topological : TopologicalOrder model)
    (intervention : Finset (Fin n)) (assigned : Fin n → X) (u : U) :
    ∃! result : Fin n → X,
      EvaluationWitness model intervention assigned u model.order (model.initial u) result := by
  have _topological : TopologicalOrder model := topological
  exact evaluation_witness_unique model intervention assigned u model.order (model.initial u)

example :
    let model : StructuralModel 1 Bool Unit :=
      { order := [0]
        order_nodup := by simp
        order_complete := by intro v; fin_cases v; simp
        parents := fun _ => ∅
        equation := fun _ _ _ => true
        initial := fun _ _ => false }
    ∃! result : Fin 1 → Bool,
      EvaluationWitness model ∅ (fun _ => false) () model.order (model.initial ()) result := by
  dsimp
  exact evaluation_witness_unique _ _ _ _ _ _

#print axioms structure_evaluation_semantics

end D5.S3.ConceptDynamics.Causal.StructuralEvaluationSemantics
