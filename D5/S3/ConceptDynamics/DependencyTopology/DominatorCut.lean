/- GID: D5/S3/ConceptDynamics/DependencyTopology/DominatorCut
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/DominatorCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A dominator is a vertex whose deletion cuts every rooted path to its target. -/

import Mathlib.Logic.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.DominatorCut
universe u

inductive DirectedPath {V : Type u} (edge : V -> V -> Prop) : V -> V -> Type u where
  | nil (v : V) : DirectedPath edge v v
  | step {first second last : V} : edge first second ->
      DirectedPath edge second last -> DirectedPath edge first last

namespace DirectedPath

def Contains {V : Type u} {edge : V -> V -> Prop} {first last : V}
    (path : DirectedPath edge first last) (vertex : V) : Prop :=
  match path with
  | .nil endpoint => vertex = endpoint
  | .step _ tail => vertex = first ∨ tail.Contains vertex

def map {V : Type u} {edge₁ edge₂ : V -> V -> Prop}
    (mapEdge : forall ⦃a b⦄, edge₁ a b -> edge₂ a b) {first last : V} :
    DirectedPath edge₁ first last -> DirectedPath edge₂ first last
  | .nil endpoint => .nil endpoint
  | .step head tail => .step (mapEdge head) (tail.map mapEdge)

theorem contains_start
    {V : Type u} {edge : V -> V -> Prop} {first last : V}
    (path : DirectedPath edge first last) : path.Contains first := by
  cases path with
  | nil => rfl
  | step => exact Or.inl rfl
end DirectedPath

def deleteVertex {V : Type u} (edge : V -> V -> Prop) (deleted : V) : V -> V -> Prop :=
  fun first second => edge first second ∧ first ≠ deleted ∧ second ≠ deleted

def Dominates {V : Type u} (root : V) (edge : V -> V -> Prop) (u v : V) : Prop :=
  forall path : DirectedPath edge root v, path.Contains u

theorem mapped_deleted_path_avoids
    {V : Type u} {edge : V -> V -> Prop} {deleted first last : V}
    (lastDifferent : deleted ≠ last)
    (path : DirectedPath (deleteVertex edge deleted) first last) :
    ¬ ((path.map fun ⦃_ _⦄ step => step.1).Contains deleted) := by
  induction path with
  | nil endpoint =>
      intro contains
      exact lastDifferent contains
  | @step first second last head tail inductionHypothesis =>
      intro contains
      change deleted = first ∨
        ((tail.map fun ⦃_ _⦄ step => step.1).Contains deleted) at contains
      rcases contains with atStart | inTail
      · exact head.2.1 atStart.symm
      · exact inductionHypothesis lastDifferent inTail

theorem unreachable_after_delete_of_dominates
    {V : Type u} {root u v : V} {edge : V -> V -> Prop}
    (dominates : Dominates root edge u v) (proper : u ≠ v) :
    ¬ Nonempty (DirectedPath (deleteVertex edge u) root v) := by
  rintro ⟨deletedPath⟩
  let originalPath : DirectedPath edge root v :=
    deletedPath.map fun ⦃_ _⦄ step => step.1
  have contains : originalPath.Contains u := dominates originalPath
  exact mapped_deleted_path_avoids proper deletedPath contains

theorem dominates_self
    {V : Type u} {root v : V} {edge : V -> V -> Prop} : Dominates root edge v v := by
  intro path
  induction path with
  | nil => rfl
  | step _ tail inductionHypothesis => exact Or.inr inductionHypothesis

#print axioms unreachable_after_delete_of_dominates
end D5.S3.ConceptDynamics.DependencyTopology.DominatorCut
