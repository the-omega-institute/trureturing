/- GID: D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.claim; result=D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.result; claim=D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.claim
   digest: The edgeless two-vertex graph cannot be any actual global coalition graph. -/

import D5.S3.ConceptDynamics.GraphColoring.GraphCoverDomination
import Mathlib.Order.Setoid.Partition
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
The model is that of Anholcer, Besharati, Mojdeh and Samadzadeh,
Global coalitions in graphs, arXiv:2509.15386v4, Definitions 1--2 and
Section 7 Problem 58. The earlier alias is v1 Section 6 Problem 4.
The current question uses the paper's order-at-least-two convention.
The earlier unrestricted order convention is a separate boundary.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/23084.

Domination is the existing imported SimpleGraph.IsDominating, including its
source attribution. Complement and graph isomorphism are native SimpleGraph
operations. A partition here has arbitrary blocks, with no independence or
maximality condition and no exceptional singleton dominating block.

The claim ranges over arbitrary finite vertex types, not a labeled host family.
The only specifically labeled graph in the proof is the legal target on Fin 2.
No realization claim for all isolate-free targets is asserted.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.GlobalCoalitionUniversality

universe u v

/-- Global domination in the host and its loopless complement on the same vertices. -/
def GloballyDominating {V : Type u} (G : SimpleGraph V) (A : Set V) : Prop :=
  G.IsDominating A ∧ Gᶜ.IsDominating A

/-- The full global-coalition relation on actual subsets of the host vertices. -/
def GlobalCoalition {V : Type u} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ¬ GloballyDominating G A ∧ ¬ GloballyDominating G B ∧
    GloballyDominating G (A ∪ B)

/-- A nonempty-block disjoint cover with a distinct actual coalition partner per block. -/
structure GCPartition {V : Type u} (G : SimpleGraph V) where
  blocks : Set (Set V)
  isPartition : Setoid.IsPartition blocks
  partners : ∀ A ∈ blocks, ∃ B ∈ blocks, B ≠ A ∧ GlobalCoalition G A B

/-- Vertices are actual partition blocks; adjacency is exactly actual global coalition. -/
def globalCoalitionGraph {V : Type u} (G : SimpleGraph V) (π : GCPartition G) :
    SimpleGraph {A : Set V // A ∈ π.blocks} where
  Adj A B := GlobalCoalition G A.val B.val
  symm := ⟨by
    intro A B h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, by
      simpa only [Set.union_comm] using h.2.2.2⟩⟩
  loopless := ⟨by
    intro A h
    exact h.2.1 (by simpa only [Set.union_self] using h.2.2.2)⟩

/-- The entire current Problem 58, with every target, host and eligible partition in scope. -/
def claim : Prop :=
  ∀ (V : Type) [Finite V], 2 ≤ Nat.card V → ∀ H : SimpleGraph V,
    ∃ (W : Type) (_ : Finite W) (G : SimpleGraph W), 2 ≤ Nat.card W ∧
      ∃ π : GCPartition G, Nonempty (globalCoalitionGraph G π ≃g H)

/-- The actual partner requirement excludes every nonempty edgeless target for every host. -/
private theorem no_edgeless_realization {V : Type u} {W : Type v} [Nonempty W]
    (G : SimpleGraph V) (π : GCPartition G) :
    ¬ Nonempty (globalCoalitionGraph G π ≃g (⊥ : SimpleGraph W)) := by
  rintro ⟨e⟩
  let A := e.symm (Classical.choice (inferInstance : Nonempty W))
  obtain ⟨B, hB, _, hcoalition⟩ := π.partners A.val A.property
  have hadj : (globalCoalitionGraph G π).Adj A ⟨B, hB⟩ := hcoalition
  have hbot := e.map_adj_iff.mpr hadj
  exact (SimpleGraph.bot_adj _ _).mp hbot

/-- Negation of the complete current universal assertion, rather than a selected-host failure. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨W, _, G, _, π, he⟩ := h (Fin 2) (by simp) (⊥ : SimpleGraph (Fin 2))
  exact no_edgeless_realization G π he

end D5.S3.Combinatorics.Graph.Domination.GlobalCoalitionUniversality
