/- GID: D5/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prerequisite and consequence closures depend only on reachability, not the chosen direct-edge presentation. -/

import D5.S3.ConceptDynamics.DagCompletion.ConsequenceClosure
import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.ReachabilityProjectionInvariance

open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
open D5.S3.ConceptDynamics.DagCompletion.ConsequenceClosure
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

/-- Two edge presentations are reachability-equivalent when they induce the same thin reachability relation. -/
def SameReachability {V : Type*}
    (first second : V → V → Prop) : Prop :=
  ∀ source target,
    Reachable first source target ↔ Reachable second source target

/-- Reachability equivalence is reflexive. -/
theorem sameReachability_refl
    {V : Type*} (edge : V → V → Prop) : SameReachability edge edge := by
  intro source target
  rfl

/-- Reachability equivalence is symmetric. -/
theorem SameReachability.symm
    {V : Type*} {first second : V → V → Prop}
    (same : SameReachability first second) :
    SameReachability second first := by
  intro source target
  exact (same source target).symm

/-- Reachability equivalence is transitive. -/
theorem SameReachability.trans
    {V : Type*} {first second third : V → V → Prop}
    (firstSecond : SameReachability first second)
    (secondThird : SameReachability second third) :
    SameReachability first third := by
  intro source target
  exact (firstSecond source target).trans (secondThird source target)

/-- Reachability-equivalent graphs have identical prerequisite closures. -/
theorem prerequisiteClosure_eq
    {V : Type*} {first second : V → V → Prop}
    (same : SameReachability first second) (targets : Set V) :
    prerequisiteClosure first targets = prerequisiteClosure second targets := by
  ext node
  constructor
  · rintro ⟨target, targetIn, path⟩
    exact ⟨target, targetIn, (same node target).1 path⟩
  · rintro ⟨target, targetIn, path⟩
    exact ⟨target, targetIn, (same node target).2 path⟩

/-- Reachability-equivalent graphs have identical consequence closures. -/
theorem consequenceClosure_eq
    {V : Type*} {first second : V → V → Prop}
    (same : SameReachability first second) (sources : Set V) :
    consequenceClosure first sources = consequenceClosure second sources := by
  ext node
  constructor
  · rintro ⟨source, sourceIn, path⟩
    exact ⟨source, sourceIn, (same source node).1 path⟩
  · rintro ⟨source, sourceIn, path⟩
    exact ⟨source, sourceIn, (same source node).2 path⟩

/-- Adding a direct edge already implied by reachability does not change reachability. -/
theorem sameReachability_insert_redundant
    {V : Type*} (edge : V → V → Prop) {source target : V}
    (redundant : Reachable edge source target) :
    SameReachability edge
      (fun first second => edge first second ∨ (first = source ∧ second = target)) := by
  intro first last
  constructor
  · intro path
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ edgeStep inductionHypothesis =>
        exact inductionHypothesis.tail (Or.inl edgeStep)
  · intro path
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ edgeStep inductionHypothesis =>
        rcases edgeStep with originalEdge | ⟨firstEq, secondEq⟩
        · exact inductionHypothesis.tail originalEdge
        · subst firstEq
          subst secondEq
          exact inductionHypothesis.trans redundant

#print axioms prerequisiteClosure_eq
#print axioms sameReachability_insert_redundant

end D5.S3.ConceptDynamics.DagCompletion.ReachabilityProjectionInvariance
