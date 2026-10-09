/- GID: D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every vertex is an identity Seidel switch exactly at graph order one. -/

/-
proof_shape: result: bind-only
escape_witness: none
switch_degree_balance: proof_shape: bind-only; consumers: vertex_degree_at, vertex_degree_off.
vertex_degree_at: proof_shape: bind-only; consumer: vertex_edge_balance.
vertex_degree_off: proof_shape: bind-only; consumer: result.
vertex_edge_balance: proof_shape: bind-only; consumer: result.
admission_basis: open-problem-resolution (#14446; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.SeidelSwitching.VertexIdentitySwitches

open Finset SimpleGraph
open scoped Classical

variable {V : Type}

/-- Complement precisely the pairs crossing the cut determined by S. -/
def seidelSwitch (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (G.Adj x y ↔ (x ∈ S ↔ y ∈ S))
  symm := ⟨fun x y h => ⟨h.1.symm, (G.adj_comm y x).trans (h.2.trans Iff.comm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A singleton switch is identity when the switched graph is isomorphic to G. -/
def IsVertexISS (G : SimpleGraph V) (x : V) : Prop :=
  Nonempty (seidelSwitch G {x} ≃g G)

/-- The complete characterization requested in Gervacio's Problem 6.1. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V),
    (∀ x, IsVertexISS G x) ↔ Fintype.card V = 1

private theorem switch_degree_balance [Fintype V]
    (G : SimpleGraph V) (S : Set V) (y : V) :
    (seidelSwitch G S).degree y +
        2 * ((G.neighborFinset y).filter (fun z => ¬ (y ∈ S ↔ z ∈ S))).card =
      G.degree y + (univ.filter (fun z => ¬ (y ∈ S ↔ z ∈ S))).card := by
  classical
  let A := G.neighborFinset y
  let B := (seidelSwitch G S).neighborFinset y
  let C := univ.filter (fun z => ¬ (y ∈ S ↔ z ∈ S))
  have hsame : B \ C = A \ C := by
    ext z
    simp only [B, A, C, mem_sdiff, mem_neighborFinset, mem_filter, mem_univ,
      true_and]
    change (_ ≠ _ ∧ (_ ↔ _)) ∧ _ ↔ _
    by_cases he : y = z
    · subst z; simp
    · tauto
  have hcross : B ∩ C = C \ A := by
    ext z
    simp only [B, A, C, mem_inter, mem_sdiff, mem_neighborFinset, mem_filter,
      mem_univ, true_and]
    change (_ ≠ _ ∧ (_ ↔ _)) ∧ _ ↔ _
    by_cases he : y = z
    · subst z; simp
    · tauto
  have hfilter : A.filter (fun z => ¬ (y ∈ S ↔ z ∈ S)) = A ∩ C := by
    ext z; simp [C]
  have hA := card_sdiff_add_card_inter A C
  have hB := card_sdiff_add_card_inter B C
  have hC := card_sdiff_add_card_inter C A
  rw [hsame, hcross] at hB
  rw [inter_comm C A] at hC
  change B.card + 2 * (A.filter (fun z => ¬ (y ∈ S ↔ z ∈ S))).card =
    A.card + C.card
  rw [hfilter]
  omega

private theorem vertex_degree_at [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (seidelSwitch G {v}).degree v + G.degree v = Fintype.card V - 1 := by
  classical
  have h := switch_degree_balance G {v} v
  simp only [Set.mem_singleton_iff, true_iff] at h
  have hA : (G.neighborFinset v).filter (fun z => z ≠ v) = G.neighborFinset v :=
    Finset.filter_true_of_mem (fun z hz => (G.mem_neighborFinset v z).mp hz |>.ne.symm)
  have hC : (univ : Finset V).filter (fun z => z ≠ v) = univ.erase v := by
    ext z; simp
  simp only [hA, hC, Finset.card_erase_of_mem (mem_univ v), card_univ,
    G.card_neighborFinset_eq_degree] at h
  omega

private theorem vertex_degree_off [Fintype V]
    (G : SimpleGraph V) (v y : V) (hy : y ≠ v) :
    (seidelSwitch G {v}).degree y + (if G.Adj y v then 2 else 0) =
      G.degree y + 1 := by
  classical
  have h := switch_degree_balance G {v} y
  simp only [Set.mem_singleton_iff, hy, false_iff, not_not] at h
  have hA : (G.neighborFinset y).filter (fun z => z = v) =
      if G.Adj y v then {v} else ∅ := by
    ext z
    by_cases ha : G.Adj y v
    · simp only [ha, if_true, mem_filter, mem_neighborFinset, mem_singleton]
      constructor
      · exact And.right
      · intro hz; subst z; exact ⟨ha, rfl⟩
    · simp only [ha, if_false, mem_filter, mem_neighborFinset, notMem_empty, iff_false,
        not_and]
      intro hz he; subst z; exact ha hz
  have hC : (univ : Finset V).filter (fun z => z = v) = {v} := by
    ext z; simp
  rw [hA, hC] at h
  by_cases ha : G.Adj y v <;> simpa [ha] using h

private theorem vertex_edge_balance [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (seidelSwitch G {v}).edgeFinset.card + 2 * G.degree v =
      G.edgeFinset.card + (Fintype.card V - 1) := by
  classical
  let H := seidelSwitch G {v}
  have hrest : H.edgeFinset \ H.incidenceFinset v =
      G.edgeFinset \ G.incidenceFinset v := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [mem_sdiff, mem_edgeFinset, mem_incidenceFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.mk'_mem_incidenceSet_iff]
      change (x ≠ y ∧ (G.Adj x y ↔ (x ∈ ({v} : Set V) ↔ y ∈ ({v} : Set V)))) ∧
        ¬ ((x ≠ y ∧ (G.Adj x y ↔ (x ∈ ({v} : Set V) ↔ y ∈ ({v} : Set V)))) ∧
          (v = x ∨ v = y)) ↔ G.Adj x y ∧ ¬ (G.Adj x y ∧ (v = x ∨ v = y))
      simp only [Set.mem_singleton_iff]
      by_cases hx : x = v
      · subst x; simp
      · by_cases hy : y = v
        · subst y; simp
        · simp only [hx, hy, iff_true]
          have hne := @SimpleGraph.Adj.ne V G x y
          tauto
  have hG := card_sdiff_add_card_eq_card (G.incidenceFinset_subset v)
  have hH := card_sdiff_add_card_eq_card (H.incidenceFinset_subset v)
  rw [hrest, H.card_incidenceFinset_eq_degree] at hH
  rw [G.card_incidenceFinset_eq_degree] at hG
  have hv := vertex_degree_at G v
  change H.degree v + G.degree v = Fintype.card V - 1 at hv
  change H.edgeFinset.card + 2 * G.degree v =
    G.edgeFinset.card + (Fintype.card V - 1)
  omega

/-- Every vertex is a vertex-ISS if and only if the graph has one vertex. -/
theorem result : claim := by
  classical
  intro V _ _ _ G
  constructor
  · intro hall
    have hdeg : ∀ v, 2 * G.degree v = Fintype.card V - 1 := by
      intro v
      obtain ⟨f⟩ := hall v
      have h := vertex_edge_balance G v
      rw [f.card_edgeFinset_eq] at h
      omega
    obtain ⟨v⟩ := ‹Nonempty V›
    by_contra hn
    have hnpos := Fintype.card_pos (α := V)
    have hdpos : 0 < G.degree v := by have := hdeg v; omega
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hdpos
    obtain ⟨f⟩ := hall v
    have hoff := vertex_degree_off G v w hw.ne.symm
    rw [if_pos hw.symm] at hoff
    have hf := f.degree_eq w
    have hwdeg := hdeg w
    have hfdeg := hdeg (f w)
    omega
  · intro hcard x
    have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have heq : seidelSwitch G {x} = G := by
      ext y z
      have hyz : y = z := Subsingleton.elim y z
      subst z
      simp [seidelSwitch]
    unfold IsVertexISS
    rw [heq]
    exact ⟨SimpleGraph.Iso.refl⟩

end D5.S3.Combinatorics.Graph.SeidelSwitching.VertexIdentitySwitches
