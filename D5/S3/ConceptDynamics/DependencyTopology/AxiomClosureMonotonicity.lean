/- GID: D5/S3/ConceptDynamics/DependencyTopology/AxiomClosureMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/AxiomClosureMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Edge-local monotone labels remain monotone along dependency reachability. -/

import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
import Mathlib.Data.Set.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.AxiomClosureMonotonicity
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

theorem value_mono_of_edge_mono
    {V Label : Type*} [Preorder Label] {edge : V -> V -> Prop} {value : V -> Label}
    (edgeMono : forall ⦃u v⦄, edge u v -> value u ≤ value v)
    {u v : V} (reachable : Reachable edge u v) : value u ≤ value v := by
  induction reachable with
  | refl => exact le_rfl
  | tail previous edgeStep inductionHypothesis =>
      exact le_trans inductionHypothesis (edgeMono edgeStep)

theorem label_mono_of_edge_mono
    {V Atom : Type*} {edge : V -> V -> Prop} {label : V -> Set Atom}
    (edgeMono : forall ⦃u v⦄, edge u v -> label u ⊆ label v)
    {u v : V} (reachable : Reachable edge u v) : label u ⊆ label v :=
  value_mono_of_edge_mono (Label := Set Atom) (value := label)
    edgeMono reachable

theorem label_mono_of_edge
    {V Atom : Type*} {edge : V -> V -> Prop} {label : V -> Set Atom}
    (edgeMono : forall ⦃u v⦄, edge u v -> label u ⊆ label v)
    {u v : V} (edgeStep : edge u v) : label u ⊆ label v :=
  label_mono_of_edge_mono edgeMono (reachable_of_edge edgeStep)

#print axioms label_mono_of_edge_mono
end D5.S3.ConceptDynamics.DependencyTopology.AxiomClosureMonotonicity
