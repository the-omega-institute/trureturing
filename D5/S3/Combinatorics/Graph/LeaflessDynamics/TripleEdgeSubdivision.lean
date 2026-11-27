/- GID: D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-segment subdivision retains incidence, connectivity, and degree-one vertices. -/

import D5.S3.ConceptDynamics.Coding.EssentialWordRealization
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Each original edge is assigned two distinct interior vertices. This gives a simple
graph even when an original edge is a loop or shares endpoints with another edge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision

open Set SimpleGraph
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (DirectedMultigraph)

variable {V E : Type*} (M : DirectedMultigraph V E)

/-- The two incidences of each original edge, indexed by edge identity. -/
abbrev Flag (E : Type*) := E ⊕ E

/-- The vertex incident to the given original flag. -/
def endpoint : Flag E → V := Sum.elim M.source M.target

/-- The underlying unoriented adjacency of the original multigraph. -/
def step (u v : V) : Prop :=
  ∃ e : E, (M.source e = u ∧ M.target e = v) ∨ (M.source e = v ∧ M.target e = u)

/-- Subdivide each named edge into three segments. The two flags become its interior vertices. -/
def graph : SimpleGraph (V ⊕ Flag E) where
  Adj
    | .inl v, .inr f => endpoint M f = v
    | .inr f, .inl v => endpoint M f = v
    | .inr (.inl e), .inr (.inr e') => e = e'
    | .inr (.inr e), .inr (.inl e') => e = e'
    | _, _ => False
  symm := by
    constructor
    intro x y h
    rcases x with x | (x | x) <;> rcases y with y | (y | y) <;>
      first | exact h | exact h.symm
  loopless := by
    constructor
    intro x
    rcases x with x | (x | x) <;> exact id

private theorem original_reachable (u v : V) (h : Relation.ReflTransGen (step M) u v) :
    (graph M).Reachable (.inl u) (.inl v) := by
  induction h with
  | refl => exact .rfl
  | @tail w v _ hv ih =>
    apply ih.trans
    have edge (e : E) : (graph M).Reachable (.inl (M.source e)) (.inl (M.target e)) := by
      have h₁ : (graph M).Adj (.inl (M.source e)) (.inr (.inl e)) := rfl
      have h₂ : (graph M).Adj (.inr (.inl e)) (.inr (.inr e)) := rfl
      have h₃ : (graph M).Adj (.inr (.inr e)) (.inl (M.target e)) := rfl
      exact h₁.reachable.trans (h₂.reachable.trans h₃.reachable)
    obtain ⟨e, (⟨hs, ht⟩ | ⟨hs, ht⟩)⟩ := hv
    · exact hs ▸ ht ▸ edge e
    · exact ht ▸ hs ▸ (edge e).symm

/-- Original connectedness lifts through the three segments of each edge. -/
theorem connected [Nonempty V] (h : ∀ u v, Relation.ReflTransGen (step M) u v) :
    (graph M).Connected := by
  have reach (x : V ⊕ Flag E) : ∃ v : V, (graph M).Reachable x (.inl v) := by
    rcases x with v | f
    · exact ⟨v, .rfl⟩
    · have hv : (graph M).Adj (.inr f) (.inl (endpoint M f)) := by cases f <;> rfl
      exact ⟨_, hv.reachable⟩
  refine { preconnected := ?_, nonempty := inferInstance }
  intro x y
  obtain ⟨u, hx⟩ := reach x
  obtain ⟨v, hy⟩ := reach y
  exact hx.trans ((original_reachable M u v (h u v)).trans hy.symm)

private theorem original_degree (v : V) :
    ((graph M).neighborSet (.inl v)).ncard = ({f : Flag E | endpoint M f = v} : Set _).ncard := by
  have heq : (graph M).neighborSet (.inl v) =
      Sum.inr '' ({f : Flag E | endpoint M f = v} : Set _) := by
    ext x
    rcases x with x | f
    · simp [mem_neighborSet, graph]
    · change endpoint M f = v ↔ _
      simp
  rw [heq, Set.ncard_image_of_injective _ Sum.inr_injective]

private theorem leftFlag_degree (e : E) :
    ((graph M).neighborSet (.inr (.inl e))).ncard = 2 := by
  have heq : (graph M).neighborSet (.inr (.inl e)) =
      {Sum.inl (M.source e), Sum.inr (Sum.inr e)} := by
    ext x
    rcases x with x | (x | x) <;> simp [mem_neighborSet, graph, endpoint, eq_comm]
  rw [heq, Set.ncard_pair (by simp)]

private theorem rightFlag_degree (e : E) :
    ((graph M).neighborSet (.inr (.inr e))).ncard = 2 := by
  have heq : (graph M).neighborSet (.inr (.inr e)) =
      {Sum.inl (M.target e), Sum.inr (Sum.inl e)} := by
    ext x
    rcases x with x | (x | x) <;> simp [mem_neighborSet, graph, endpoint, eq_comm]
  rw [heq, Set.ncard_pair (by simp)]

/-- Subdivision retains each original incidence count and inserts vertices of degree two. -/
theorem neighbor_ncard_le_of_incident_flags_le {D : ℕ} (hD : 2 ≤ D)
    (hflags : ∀ v, ({f : Flag E | endpoint M f = v} : Set _).ncard ≤ D) (w : V ⊕ Flag E) :
    ((graph M).neighborSet w).ncard ≤ D := by
  rcases w with v | (e | e)
  · simpa only [original_degree] using hflags v
  · rwa [leftFlag_degree]
  · rwa [rightFlag_degree]

/-- Every leaf is an original vertex with one incident flag. A loop contributes both flags. -/
theorem leafless_iff :
    (∀ w, ((graph M).neighborSet w).ncard ≠ 1) ↔
      ∀ v, ({f : Flag E | endpoint M f = v} : Set _).ncard ≠ 1 := by
  constructor
  · intro h v
    simpa only [original_degree] using h (.inl v)
  · intro h w
    rcases w with v | (e | e)
    · simpa only [original_degree] using h v
    · rw [leftFlag_degree]
      decide
    · rw [rightFlag_degree]
      decide

/--
info: 'D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision.connected' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms connected

/--
info: 'D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision.leafless_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms leafless_iff

end D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision
