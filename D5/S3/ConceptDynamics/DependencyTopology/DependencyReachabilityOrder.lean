/- GID: D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Acyclic dependency reachability is a partial order. -/

import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib provides `Relation.ReflTransGen`, `Relation.TransGen`,
     `reflTransGen_iff_eq_or_transGen`, and their transitivity laws.
   * Repository searches found no accepted declaration packaging the
     acyclic-reachability partial-order theorem for an arbitrary edge relation.
   * The statement remains independent of repository modules and import graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

def Reachable {V : Type*} (edge : V -> V -> Prop) : V -> V -> Prop :=
  Relation.ReflTransGen edge

def StrictReachable {V : Type*} (edge : V -> V -> Prop) : V -> V -> Prop :=
  Relation.TransGen edge

def AcyclicEdge {V : Type*} (edge : V -> V -> Prop) : Prop :=
  forall v, ¬ StrictReachable edge v v

@[refl] theorem reachable_refl {V : Type*} (edge : V -> V -> Prop) (v : V) :
    Reachable edge v v := Relation.ReflTransGen.refl

@[trans] theorem reachable_trans {V : Type*} {edge : V -> V -> Prop} {u v w : V}
    (huv : Reachable edge u v) (hvw : Reachable edge v w) : Reachable edge u w :=
  huv.trans hvw

instance {V : Type*} (edge : V -> V -> Prop) : Std.Refl (Reachable edge) :=
  ⟨reachable_refl edge⟩

instance {V : Type*} (edge : V -> V -> Prop) : IsTrans V (Reachable edge) :=
  ⟨fun _ _ _ huv hvw => reachable_trans huv hvw⟩

theorem reachable_of_edge {V : Type*} {edge : V -> V -> Prop} {u v : V}
    (huv : edge u v) : Reachable edge u v := Relation.ReflTransGen.single huv

theorem reachable_iff_eq_or_strict {V : Type*} {edge : V -> V -> Prop} {u v : V} :
    Reachable edge u v <-> v = u ∨ StrictReachable edge u v :=
  Relation.reflTransGen_iff_eq_or_transGen

theorem reachable_antisymm_of_acyclic
    {V : Type*} {edge : V -> V -> Prop} (acyclic : AcyclicEdge edge)
    {u v : V} (huv : Reachable edge u v) (hvu : Reachable edge v u) : u = v := by
  rcases reachable_iff_eq_or_strict.mp huv with huvEq | huvStrict
  · exact huvEq.symm
  rcases reachable_iff_eq_or_strict.mp hvu with hvuEq | hvuStrict
  · exact hvuEq
  exact (acyclic u (huvStrict.trans hvuStrict)).elim

theorem reachable_partial_order
    {V : Type*} {edge : V -> V -> Prop} (acyclic : AcyclicEdge edge) :
    Reflexive (Reachable edge) ∧ Transitive (Reachable edge) ∧
      (∀ ⦃u v⦄, Reachable edge u v → Reachable edge v u → u = v) := by
  refine ⟨reachable_refl edge, ?_, ?_⟩
  · intro u v w huv hvw
    exact reachable_trans huv hvw
  intro u v huv hvu
  exact reachable_antisymm_of_acyclic acyclic huv hvu

example :
    let edge : Bool -> Bool -> Prop := fun u v => u = false ∧ v = true
    Reachable edge false true := by
  dsimp
  exact reachable_of_edge ⟨rfl, rfl⟩

#print axioms reachable_partial_order
end D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
