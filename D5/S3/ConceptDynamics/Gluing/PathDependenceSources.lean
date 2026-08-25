/- GID: D5/S3/ConceptDynamics/Gluing/PathDependenceSources
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/PathDependenceSources
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Word order and transition incompatibility independently produce path dependence. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Order.Closure
import Mathlib.Order.Hom.CompleteLattice

/- Library-search audit trail (2026-08-25):
   * Repository searches for word-order residuals, path dependence, commuting
     local closures, and transition incompatibility found no combined theorem.
     `PureReadoutOrderIndependence` and `GlobalFrameCoboundaryCriterion` are
     adjacent results, but neither supplies either countermodel below.
   * Body-shape searches found the canonical `runWord` primitive in
     `ControlledBehaviorUniversality`; it is imported and used directly for the
     action-word witness.
   * Exact pinned-Mathlib hits `ClosureOperator.mk'`, `Function.Commute`, and
     `Equiv.toOrderIsoSet` construct the local closures and their bijective
     transition. No library theorem packages the two independent sources. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.PathDependenceSources

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- Path dependence has two independent sources. Noncommuting actions leave a
word-order residual on a globally trivial product carrier. Separately, two
distinct local closure operators can commute while a bijective chart transition
fails to intertwine one of them. -/
theorem path_dependence_has_two_sources :
    (let update : Bool -> Unit × Bool -> Unit × Bool :=
        fun action state =>
          (state.1, if action then false else !state.2);
      runWord update [false, true] ((), false) ≠
        runWord update [true, false] ((), false)) ∧
    (let addFalse : ClosureOperator (Set Bool) :=
        ClosureOperator.mk' (fun set => set ∪ {false})
          (fun _ _ subset => Set.union_subset_union subset (fun _ member => member))
          (fun _ => Set.subset_union_left)
          (fun _ => by simp);
      let addTrue : ClosureOperator (Set Bool) :=
        ClosureOperator.mk' (fun set => set ∪ {true})
          (fun _ _ subset => Set.union_subset_union subset (fun _ member => member))
          (fun _ => Set.subset_union_left)
          (fun _ => by simp);
      let transition : Set Bool ≃o Set Bool :=
        Equiv.toOrderIsoSet (Equiv.swap false true);
      Function.Commute addFalse addTrue ∧
        transition (addFalse ∅) ≠ addFalse (transition ∅)) := by
  constructor
  · decide
  · dsimp only
    refine ⟨?_, ?_⟩
    · intro set
      ext value
      change value ∈ (set ∪ {true}) ∪ {false} ↔
        value ∈ (set ∪ {false}) ∪ {true}
      simp only [Set.mem_union, Set.mem_singleton_iff]
      aesop
    · intro compatible
      have falseMembership := congrArg (fun set : Set Bool => false ∈ set) compatible
      simp [Equiv.toOrderIsoSet] at falseMembership

#print axioms path_dependence_has_two_sources

end D5.S3.ConceptDynamics.Gluing.PathDependenceSources
