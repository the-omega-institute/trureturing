/- GID: D5/S3/Combinatorics/Graph/Walks/ConnectivityFan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ConnectivityFan
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Vertex-deletion connectivity supplies terminal-clean fans of the full minimum size. -/
import D5.S3.Combinatorics.Graph.Walks.MengerCertificates
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in
docs/reports/licenses/menger-hamiltonian-LICENSE.txt.
Authors: Juan Pablo Traverso Gianini

Adapted from MengerHamilton/ChvatalErdosAux.lean, exists_fan, in
jtraverso/menger-hamiltonian at 35c5f684f9bfbd244bd0999ce725623ab571adb6.
The terminal set is an arbitrary finite set rather than a cyclic array.
The original receiver MengerCertificates.Fam supplies terminal cleanliness.
Source pins: Lean v4.35.0-rc3, Mathlib c55e6e786f49471c72fbddbec5415808896aec1e.
Receiver pins: Lean v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ConnectivityFan

open SimpleGraph

universe u
variable {V : Type u}

private lemma exists_path_avoiding {G : SimpleGraph V} (S : Set V)
    (hS : (G.induce Sᶜ).Connected) {a b : V} (ha : a ∉ S) (hb : b ∉ S) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ y ∈ p.support, y ∉ S := by
  classical
  obtain ⟨walk⟩ := hS.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨(walk.map (Embedding.induce Sᶜ).toHom).bypass, Walk.bypass_isPath _, ?_⟩
  intro y hy
  have hmem := Walk.support_bypass_subset_support _ hy
  erw [Walk.support_map, List.mem_map] at hmem
  obtain ⟨z, _, rfl⟩ := hmem
  exact z.2

/-- A fan to an arbitrary finite terminal set, with no lower bound on its size. -/
theorem exists_fan [Finite V] {G : SimpleGraph V} {k : ℕ}
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    (B : Finset V) {x : V} (hx : x ∉ B) :
    ∃ (endpoint : Fin (min k B.card) → V)
      (paths : ∀ index, G.Walk x (endpoint index)),
      (∀ index, endpoint index ∈ B ∧ (paths index).IsPath ∧
        ∀ y ∈ (paths index).support, y ∈ B → y = endpoint index) ∧
      (∀ left right, left ≠ right → ∀ y ∈ (paths left).support,
        y ∈ (paths right).support → y = x) ∧ Function.Injective endpoint := by
  classical
  letI := Fintype.ofFinite V
  let H := G.deleteEdges {edge | x ∈ edge}
  have hle : H ≤ G := G.deleteEdges_le _
  have hHx : ∀ y, ¬ H.Adj x y := by intro y hy; simp [H] at hy
  let A := G.neighborFinset x
  have hxA : x ∉ A := by simp [A]
  have hsep : ∀ X, MengerCertificates.Separates H A B X → min k B.card ≤ X.card := by
    intro X hX
    by_contra hsmall
    have hXk : X.card < k := lt_of_lt_of_le (Nat.lt_of_not_ge hsmall) (min_le_left _ _)
    have hXB : X.card < B.card := lt_of_lt_of_le (Nat.lt_of_not_ge hsmall) (min_le_right _ _)
    obtain ⟨terminal, hterminalB, hterminalX⟩ : ∃ terminal ∈ B, terminal ∉ X := by
      by_contra hnone
      push Not at hnone
      exact (not_le_of_gt hXB) (Finset.card_le_card hnone)
    let S : Set V := ↑(X.erase x)
    have hSk : S.ncard < k := by
      rw [Set.ncard_coe_finset]
      exact lt_of_le_of_lt Finset.card_erase_le hXk
    obtain ⟨walk, hpath, havoid⟩ := exists_path_avoiding S (hconn S hSk) (a := x) (b := terminal)
      (by simp [S]) (by simp [S, hterminalX])
    have hne : x ≠ terminal := fun heq => hx (heq ▸ hterminalB)
    obtain ⟨first, hfirst, rest, rfl⟩ := Walk.exists_eq_cons_of_ne hne walk
    rw [Walk.cons_isPath_iff] at hpath
    have hrest : ∀ edge ∈ rest.edges, edge ∉ {edge : Sym2 V | x ∈ edge} := by
      intro edge hedge hxedge
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hxedge
      exact hpath.2 (rest.fst_mem_support_of_mem_edges hedge)
    obtain ⟨vertex, hvertexX, hvertexRest⟩ := hX first (by simpa [A] using hfirst)
      terminal hterminalB (rest.toDeleteEdges {edge | x ∈ edge} hrest)
    have hmem : vertex ∈ rest.support := by
      simp only [Walk.toDeleteEdges] at hvertexRest
      rwa [Walk.support_transfer] at hvertexRest
    have hvx : vertex ≠ x := fun heq => hpath.2 (heq ▸ hmem)
    exact havoid vertex (by simp [hmem]) (by simp [S, hvertexX, hvx])
  obtain ⟨family, hfamily, hdisjoint⟩ :=
    MengerCertificates.fam_of_le H.edgeSet.ncard H rfl A B (min k B.card) hsep
  have hmissing : ∀ index, x ∉ (family index).2.2.support := by
    intro index hmem
    have hne : x ≠ (family index).1 := fun heq => hxA (heq ▸ (hfamily index).1)
    obtain ⟨first, hfirst, _, _⟩ := Walk.exists_eq_cons_of_ne hne
      (((family index).2.2.takeUntil x hmem).reverse)
    exact hHx first hfirst
  let paths : ∀ index, G.Walk x (family index).2.1 := fun index =>
    Walk.cons (by simpa [A] using (hfamily index).1) ((family index).2.2.mapLe hle)
  refine ⟨fun index => (family index).2.1, paths, ?_, ?_, ?_⟩
  · intro index
    refine ⟨(hfamily index).2.1, ?_, ?_⟩
    · simp only [paths, Walk.cons_isPath_iff, Walk.support_mapLe_eq_support]
      exact ⟨(hfamily index).2.2.1.mapLe hle, hmissing index⟩
    · intro y hy hyB
      simp only [paths, Walk.support_cons, Walk.support_mapLe_eq_support, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact (hx hyB).elim
      · exact (hfamily index).2.2.2.2 y hy hyB
  · intro left right hne y hleft hright
    simp only [paths, Walk.support_cons, Walk.support_mapLe_eq_support, List.mem_cons] at hleft hright
    rcases hleft with rfl | hleft
    · rfl
    rcases hright with rfl | hright
    · rfl
    exact (hdisjoint left right hne y hleft hright).elim
  · intro left right heq
    by_contra hne
    exact hdisjoint left right hne _ (family left).2.2.end_mem_support
      (by simpa only [heq] using (family right).2.2.end_mem_support)

end D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
