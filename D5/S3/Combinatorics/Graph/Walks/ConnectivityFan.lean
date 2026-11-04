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
import D5.S3.Combinatorics.Graph.Brooks.ColoringExtension
import Mathlib.Combinatorics.SimpleGraph.Acyclic

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
open scoped Classical

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

private lemma exists_cycle [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hn : 3 ≤ Fintype.card V) (hk : 2 ≤ k)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) :
    ∃ base, ∃ cycle : G.Walk base base, cycle.IsCycle := by
  classical
  by_contra hnone
  push Not at hnone
  have hacyclic : G.IsAcyclic := fun base cycle hcycle => hnone base cycle hcycle
  have hconnected : G.Connected := by
    have hempty := hconn ∅ (by simp; omega)
    have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    refine ⟨fun left right => ?_⟩
    obtain ⟨path, _, _⟩ := exists_path_avoiding ∅ hempty
      (Set.notMem_empty left) (Set.notMem_empty right)
    exact path.reachable
  have htree : G.IsTree := ⟨hconnected, hacyclic⟩
  have hdegree : ∀ vertex, 2 ≤ G.degree vertex := by
    intro vertex
    by_contra hsmall
    have hneighbors : (G.neighborFinset vertex : Set V).ncard < k := by
      rw [Set.ncard_coe_finset, card_neighborFinset_eq_degree]
      omega
    obtain ⟨other, hother⟩ : ∃ other, other ∉ insert vertex (G.neighborFinset vertex) := by
      by_contra hfull
      push Not at hfull
      have hcard := Finset.card_le_card
        (show Finset.univ ⊆ insert vertex (G.neighborFinset vertex) from fun other _ => hfull other)
      rw [Finset.card_univ] at hcard
      have hbound := Finset.card_insert_le vertex (G.neighborFinset vertex)
      rw [card_neighborFinset_eq_degree] at hbound
      omega
    simp only [Finset.mem_insert, not_or] at hother
    obtain ⟨path, _, havoid⟩ := exists_path_avoiding (G.neighborFinset vertex : Set V)
      (hconn _ hneighbors) (a := vertex) (b := other) (by simp) (by simpa using hother.2)
    obtain ⟨first, hfirst, rest, rfl⟩ := Walk.exists_eq_cons_of_ne (Ne.symm hother.1) path
    exact havoid first (by simp) (by simpa using hfirst)
  have htreeEdges := htree.card_edgeFinset
  have hdegrees := G.sum_degrees_eq_twice_card_edges
  have hlower : ∑ _vertex : V, 2 ≤ ∑ vertex, G.degree vertex :=
    Finset.sum_le_sum fun vertex _ => hdegree vertex
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlower
  omega

private lemma induced_cycle_spans_support {G : SimpleGraph V} {base : V}
    (cycle : G.Walk base base) (hcycle : cycle.IsCycle) :
    (cycle.induce {vertex | vertex ∈ cycle.support} (fun _ hmem => hmem)).IsHamiltonianCycle := by
  classical
  apply Walk.isHamiltonianCycle_iff_isCycle_and_forall_mem_support.mpr
  constructor
  · rw [← Walk.isCycle_map_iff_of_injective
      (f := (Embedding.induce {vertex | vertex ∈ cycle.support}).toHom) Subtype.val_injective,
      Walk.map_induce]
    exact hcycle
  · intro vertex
    rw [Walk.support_induce]
    exact (List.mem_attachWith _ vertex).mpr vertex.property

/-- A longest ordinary cycle, spanning its own support, with a fan from every outside vertex. -/
theorem exists_maximal_cycle_fans [Finite V] {G : SimpleGraph V} {k : ℕ}
    (hn : 3 ≤ Nat.card V) (hk : 2 ≤ k)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) :
    ∃ base, ∃ cycle : G.Walk base base, cycle.IsCycle ∧
      (∀ otherBase (other : G.Walk otherBase otherBase),
        other.IsCycle → other.length ≤ cycle.length) ∧
      (cycle.induce {vertex | vertex ∈ cycle.support} (fun _ hmem => hmem)).IsHamiltonianCycle ∧
      ∀ x : V, x ∉ cycle.support →
        ∃ (endpoint : Fin (min k cycle.length) → V)
          (paths : ∀ index, G.Walk x (endpoint index)),
          (∀ index, endpoint index ∈ cycle.support ∧ (paths index).IsPath ∧
            ∀ y ∈ (paths index).support, y ∈ cycle.support → y = endpoint index) ∧
          (∀ left right, left ≠ right → ∀ y ∈ (paths left).support,
            y ∈ (paths right).support → y = x) ∧ Function.Injective endpoint := by
  classical
  letI := Fintype.ofFinite V
  have hn' : 3 ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hn
  obtain ⟨initialBase, initial, hinitial⟩ := exists_cycle hn' hk hconn
  have hbound : ∀ base (cycle : G.Walk base base), cycle.IsCycle →
      cycle.length ≤ Fintype.card V := by
    intro base cycle hcycle
    rw [← Walk.IsCycle.support_toFinset_card hcycle]
    exact Finset.card_le_univ _
  let predicate := fun length => ∃ base, ∃ cycle : G.Walk base base,
    cycle.IsCycle ∧ cycle.length = length
  obtain ⟨base, cycle, hcycle, hlength⟩ := Nat.findGreatest_spec (P := predicate)
    (hbound initialBase initial hinitial) ⟨initialBase, initial, hinitial, rfl⟩
  refine ⟨base, cycle, hcycle, ?_, induced_cycle_spans_support cycle hcycle, ?_⟩
  · intro otherBase other hother
    rw [hlength]
    exact Nat.le_findGreatest (P := predicate) (hbound otherBase other hother)
      ⟨otherBase, other, hother, rfl⟩
  · intro x hx
    have hfan := exists_fan hconn cycle.support.toFinset (x := x) (by simpa using hx)
    have hcard : cycle.support.toFinset.card = cycle.length :=
      Walk.IsCycle.support_toFinset_card hcycle
    rw [hcard] at hfan
    simpa only [List.mem_toFinset] using hfan

end D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
