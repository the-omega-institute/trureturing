/- GID: D5/S3/ConceptDynamics/Spacetime/ProductPaths
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ProductPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Product paths increase time and reflect order within each old component. -/

import D5.S3.ConceptDynamics.Spacetime.ProductNodes
import D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate
import D5.S3.ConceptDynamics.DagSemantics.ConservativeDagEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.ProductPaths

open D5.S0.History.Spacetime.ArchiveCarrier
open ProductNodes
open DagSemantics.StrictDependencyCoordinate
open DagSemantics.ConservativeDagEmbedding

variable {d : Nat} (c e : Context d)

/-- Exactly the two copied internal relations and the two parent edges. -/
inductive Edge : Node c e → Node c e → Prop
  | left {a b : c.Event} : c.archive.causal a b → Edge (oldLeft c e a) (oldLeft c e b)
  | right {a b : e.Event} : e.archive.causal a b → Edge (oldRight c e a) (oldRight c e b)
  | parentLeft (p : Parents c e) : Edge (oldLeft c e p.1.val) (generated c e p)
  | parentRight (p : Parents c e) : Edge (oldRight c e p.2.val) (generated c e p)

theorem edge_to_left {x : Node c e} {b : c.Event} (h : Edge c e x (oldLeft c e b)) :
    ∃ a, x = oldLeft c e a ∧ c.archive.causal a b := by
  cases h with
  | left h => exact ⟨_, rfl, h⟩

theorem edge_to_right {x : Node c e} {b : e.Event} (h : Edge c e x (oldRight c e b)) :
    ∃ a, x = oldRight c e a ∧ e.archive.causal a b := by
  cases h with
  | right h => exact ⟨_, rfl, h⟩

theorem generated_no_edge (p : Parents c e) (x : Node c e) :
    ¬ Edge c e (generated c e p) x := by intro h; cases h

theorem edge_time : StrictDependencyCoordinate (Edge c e) (fun x => (attributes c e x).time) := by
  intro x y h
  cases h with
  | left h => exact c.archive.time_lt _ _ h
  | right h => exact e.archive.time_lt _ _ h
  | parentLeft p =>
    change (c.archive.attributes p.1.val).time <
      max (c.archive.attributes p.1.val).time (e.archive.attributes p.2.val).time + 1
    omega
  | parentRight p =>
    change (e.archive.attributes p.2.val).time <
      max (c.archive.attributes p.1.val).time (e.archive.attributes p.2.val).time + 1
    omega

/-- Direct reuse of the frozen strict-coordinate path theorem. -/
theorem path_time {x y : Node c e} (h : Relation.TransGen (Edge c e) x y) :
    (attributes c e x).time < (attributes c e y).time := strict_of_transGen (edge_time c e) h

theorem path_irrefl (x : Node c e) : ¬ Relation.TransGen (Edge c e) x x :=
  acyclic_of_strictCoordinate (edge_time c e) x

/-- The preregistered invariant: a nonempty path ending in old-left stays there
and composes the old strict relation. -/
theorem path_to_left {x y : Node c e} (h : Relation.TransGen (Edge c e) x y) :
    ∀ b : c.Event, y = oldLeft c e b → ∃ a, x = oldLeft c e a ∧ c.archive.causal a b := by
  induction h with
  | single h =>
    intro b hb
    subst hb
    exact edge_to_left c e h
  | tail _ h ih =>
    intro b hb
    subst hb
    obtain ⟨m, hm, hmb⟩ := edge_to_left c e h
    obtain ⟨a, ha, ham⟩ := ih m hm
    exact ⟨a, ha, c.archive.trans _ _ _ ham hmb⟩

theorem path_to_right {x y : Node c e} (h : Relation.TransGen (Edge c e) x y) :
    ∀ b : e.Event, y = oldRight c e b → ∃ a, x = oldRight c e a ∧ e.archive.causal a b := by
  induction h with
  | single h =>
    intro b hb
    subst hb
    exact edge_to_right c e h
  | tail _ h ih =>
    intro b hb
    subst hb
    obtain ⟨m, hm, hmb⟩ := edge_to_right c e h
    obtain ⟨a, ha, ham⟩ := ih m hm
    exact ⟨a, ha, e.archive.trans _ _ _ ham hmb⟩

theorem path_left_iff (a b : c.Event) :
    Relation.TransGen (Edge c e) (oldLeft c e a) (oldLeft c e b) ↔ c.archive.causal a b := by
  constructor
  · intro h
    obtain ⟨z, hz, hzb⟩ := path_to_left c e h b rfl
    have : a = z := Sum.inl.inj (Sum.inl.inj hz)
    subst z; exact hzb
  · intro h; exact .single (.left h)

theorem path_right_iff (a b : e.Event) :
    Relation.TransGen (Edge c e) (oldRight c e a) (oldRight c e b) ↔ e.archive.causal a b := by
  constructor
  · intro h
    obtain ⟨z, hz, hzb⟩ := path_to_right c e h b rfl
    have : a = z := Sum.inr.inj (Sum.inl.inj hz)
    subst z; exact hzb
  · intro h; exact .single (.right h)

theorem generated_no_path (p : Parents c e) (x : Node c e) :
    ¬ Relation.TransGen (Edge c e) (generated c e p) x := by
  intro h
  obtain ⟨_, hh, _⟩ := Relation.TransGen.head'_iff.mp h
  exact generated_no_edge c e _ _ hh

/-- Old components have no cross paths, even when a current region is empty. -/
theorem no_cross_path (a : c.Event) (b : e.Event) :
    ¬ Relation.TransGen (Edge c e) (oldLeft c e a) (oldRight c e b) ∧
    ¬ Relation.TransGen (Edge c e) (oldRight c e b) (oldLeft c e a) := by
  constructor
  · intro h
    obtain ⟨_, hh, _⟩ := path_to_right c e h b rfl
    cases Sum.inl.inj hh
  · intro h
    obtain ⟨_, hh, _⟩ := path_to_left c e h a rfl
    cases Sum.inl.inj hh

/-- A generated event has exactly its parents and their old predecessors as ancestors. -/
theorem path_generated_iff (x : Node c e) (p : Parents c e) :
    Relation.TransGen (Edge c e) x (generated c e p) ↔
      (∃ a, x = oldLeft c e a ∧ (a = p.1.val ∨ c.archive.causal a p.1.val)) ∨
      (∃ b, x = oldRight c e b ∧ (b = p.2.val ∨ e.archive.causal b p.2.val)) := by
  rw [Relation.TransGen.tail'_iff]
  constructor
  · rintro ⟨y, hxy, hyp⟩
    cases hyp with
    | parentLeft p =>
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy with h | h
      · exact Or.inl ⟨p.1.val, h.symm, Or.inl rfl⟩
      · obtain ⟨a, ha, har⟩ := path_to_left c e h _ rfl
        exact Or.inl ⟨a, ha, Or.inr har⟩
    | parentRight p =>
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy with h | h
      · exact Or.inr ⟨p.2.val, h.symm, Or.inl rfl⟩
      · obtain ⟨b, hb, hbr⟩ := path_to_right c e h _ rfl
        exact Or.inr ⟨b, hb, Or.inr hbr⟩
  · rintro (⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩)
    · refine ⟨oldLeft c e p.1.val, ?_, .parentLeft p⟩
      rcases ha with rfl | ha
      · exact .refl
      · exact .single (.left ha)
    · refine ⟨oldRight c e p.2.val, ?_, .parentRight p⟩
      rcases hb with rfl | hb
      · exact .refl
      · exact .single (.right hb)

/-- This bridge also lets consumers transport an already supplied old path. -/
def conservativeLeft : ConservativeEmbedding c.archive.causal (Edge c e) where
  toFun := oldLeft c e
  injective := fun _ _ h => Sum.inl.inj (Sum.inl.inj h)
  map_edge := by intro a b h; exact Edge.left h
  reflect_edge := by
    intro first second h
    obtain ⟨a, ha, hab⟩ := edge_to_left c e h
    have hh := Sum.inl.inj (Sum.inl.inj ha)
    subst a; exact hab

theorem map_old_left_path {a b : c.Event} (h : Relation.TransGen c.archive.causal a b) :
    Relation.TransGen (Edge c e) (oldLeft c e a) (oldLeft c e b) :=
    (conservativeLeft c e).map_strictReachable h

end D5.S3.ConceptDynamics.Spacetime.ProductPaths
