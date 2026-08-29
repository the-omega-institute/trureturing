/- GID: D5/S3/ConceptDynamics/Governance/FiniteAcyclicJudgingGraphRoot
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/FiniteAcyclicJudgingGraphRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite nonempty acyclic judging graph has a vertex with no judges. -/

import D5.S3.ConceptDynamics.DagCompletion.WellFoundedFrontier
import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
import Mathlib.Data.Fintype.Card

/- Library-search audit trail (2026-08-29):
   * Searches in `D5/S0/Rewriting`, `D5/S1/FixedPoints`, and
     `D5/S3/ConceptDynamics` found the exact directed-acyclicity definition
     `DependencyReachabilityOrder.AcyclicEdge` and the reusable root extractor
     `WellFoundedFrontier.exists_ready_of_wellFounded`.
   * `RootedTransientTreeClassification.transient_child_well_founded` uses the
     same pinned-library bridge from an irreflexive transitive closure.
   * Pinned Mathlib v4.31.0 provides
     `Finite.wellFounded_of_trans_of_irrefl` and `Subrelation.wf`. They are used
     directly; the finite repeated-vertex argument is not reproved here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.FiniteAcyclicJudgingGraphRoot

open D5.S3.ConceptDynamics.DagCompletion.WellFoundedFrontier
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

/-- A finite nonempty directed judging graph with no directed cycle has a
vertex whose incoming judge set is empty. -/
theorem finite_acyclic_judging_graph_has_root
    {V : Type*} [Finite V] [Nonempty V]
    (judges : V -> V -> Prop)
    (acyclic : AcyclicEdge judges) :
    exists root : V, forall judge : V, ¬ judges judge root := by
  let closure := Relation.TransGen judges
  letI : Std.Irrefl closure := ⟨acyclic⟩
  have closureWellFounded : WellFounded closure :=
    Finite.wellFounded_of_trans_of_irrefl closure
  have judgesWellFounded : WellFounded judges :=
    Subrelation.wf (fun edge => Relation.TransGen.single edge) closureWellFounded
  obtain ⟨root, _rootInUniverse, ready⟩ :=
    exists_ready_of_wellFounded judgesWellFounded
      (pending := (Set.univ : Set V)) Set.univ_nonempty
  refine ⟨root, ?_⟩
  intro judge judged
  have judgeOutsideUniverse : judge ∈ (Set.univ : Set V)ᶜ := ready judged
  simpa using judgeOutsideUniverse

#print axioms finite_acyclic_judging_graph_has_root

end D5.S3.ConceptDynamics.Governance.FiniteAcyclicJudgingGraphRoot
