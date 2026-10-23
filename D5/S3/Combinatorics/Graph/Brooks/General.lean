/- GID: D5/S3/Combinatorics/Graph/Brooks/General
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Brooks/General
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Licensed general Brooks theorem with its actual clique and odd-cycle alternatives. -/

import D5.S3.Combinatorics.Graph.Brooks.Surgery
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-
Copyright (c) 2026 Brian Rabern. All rights reserved.
Released under Apache 2.0 license as described in
`docs/reports/brooks-suppliers/BrooksLean-LICENSE.txt`.
Authors: Brian Rabern and Opus 5

Source: https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d
Units: BrooksLean/OddCycle.lean, BrooksLean/VertexLemmas.lean, BrooksLean/Brooks.lean.
Modified from the retained General source by capacity partition on 2026-10-19.
Only module framing, imports and consumed helper visibility are adapted here.
The connected clique-completeness, cycle exhaustion and cycle-isomorphism
constructions are additions from the retained VC1 continuation, rather than
parts of the supplier's raw Brooks theorem.
The low-degree deletion extension is imported from its existing native owner.
The mathematical argument is Landon Rabern, Yet another proof of Brooks' theorem,
Discrete Mathematics 346 (2023), 113261, DOI 10.1016/j.disc.2022.113261.
Retire each transplanted statement when this repository's pinned Mathlib contains
an equivalent statement, replacing its consumers by direct applications.
-/

section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {n : ℕ}

private theorem brooksAux :
    ∀ (m : ℕ) {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ m → G.CliqueFree (G.maxDegree + 1) →
      (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree := by
  intro m
  induction m with
  | zero =>
    intro V G _ _ hcard _ _
    have : IsEmpty V := Fintype.card_eq_zero_iff.1 (by lia)
    exact .of_isEmpty _
  | succ k ih =>
    intro V G _ _ hcard hcf hodd
    classical
    rcases le_or_gt G.maxDegree 2 with h2 | h3
    · exact colorable_maxDegree_of_maxDegree_le_two h2 hcf hodd
    have hΔ3 : 3 ≤ G.maxDegree := h3
    set Δ := G.maxDegree with hΔdef
    rcases em (cliqueMinusEdge (Δ - 1) ⊑ G) with hH | hH
    · -- STEP 2: colouring when `G` contains `K⁻_{Δ+1}`.
      obtain ⟨φ⟩ := hH
      let S : Set V := Set.range φ
      have hcard' : Fintype.card ↥(Sᶜ : Set V) ≤ k := by
        have := Fintype.card_compl_set S
        have hS : Fintype.card ↥S = Δ + 1 := by
          dsimp [S]
          rw [Set.card_range_of_injective (f := (φ : Fin (Δ - 1 + 2) → V)) φ.injective,
            Fintype.card_fin]
          omega
        omega
      have hΔ' : (G.induce (Sᶜ : Set V)).maxDegree ≤ Δ := by
        simpa [Δ] using Copy.maxDegree_mono (Embedding.induce (Sᶜ : Set V)).toCopy
      have hcf' : (G.induce (Sᶜ : Set V)).CliqueFree (Δ + 1) := by
        intro t ht
        exact hcf _ ((isNClique_induce_iff _ t _).1 ht)
      have hcol' : (G.induce (Sᶜ : Set V)).Colorable Δ :=
        colorable_of_card_le_of_maxDegree_le (fun G => ih G) (G.induce (Sᶜ : Set V))
          hcard' hΔ3 hΔ' hcf'
      simpa [Δ] using
        Colorable.of_cliqueMinusEdge_copy (G := G) hΔ3 (le_of_eq hΔdef.symm) hcf φ hcol'
    rcases em (∃ v, G.degree v < Δ) with ⟨v, hv⟩ | hreg
    · have hcard' : Fintype.card ↥({v}ᶜ : Set V) ≤ k := by
        have := Fintype.card_compl_set ({v} : Set V)
        simp only [Set.card_singleton] at this
        omega
      have hΔ' : (G.induce ({v}ᶜ : Set V)).maxDegree ≤ Δ := by
        simpa [Δ] using Copy.maxDegree_mono (Embedding.induce ({v}ᶜ : Set V)).toCopy
      have hcf' : (G.induce ({v}ᶜ : Set V)).CliqueFree (Δ + 1) := by
        intro t ht
        exact hcf _ ((isNClique_induce_iff _ t _).1 ht)
      have hcol' : (G.induce ({v}ᶜ : Set V)).Colorable Δ :=
        colorable_of_card_le_of_maxDegree_le (fun G => ih G) (G.induce ({v}ᶜ))
          hcard' hΔ3 hΔ' hcf'
      simpa [Δ] using Colorable.of_induce_compl_singleton hcol' hv
    push Not at hreg
    have hreg' : G.IsRegularOfDegree Δ :=
      isRegularOfDegree_maxDegree_of_forall_le (by simpa [Δ] using hreg)
    obtain ⟨I, hI⟩ := exists_maximal_isIndepSet G
    -- Surgery endgame (Rabern).
    have hVne : Nonempty V := by
      by_contra hEmpty
      rw [not_nonempty_iff] at hEmpty
      have h0 : G.maxDegree = 0 := by simp [maxDegree]
      omega
    have hI_nonempty : I.Nonempty := by
      by_contra hIempty
      rw [Set.not_nonempty_iff_eq_empty] at hIempty
      rw [hIempty] at hI
      obtain ⟨v⟩ := hVne
      have hindep : G.IsIndepSet ({v} : Set V) := by
        simp [IsIndepSet, Set.pairwise_singleton]
      exact absurd (hI.2 hindep (Set.empty_subset _) (Set.mem_singleton v)) (by simp)
    have hIc_nonempty : (Iᶜ : Set V).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      obtain ⟨v⟩ := hVne
      have hdeg0 : G.degree v = 0 := by
        rw [← card_neighborFinset_eq_degree]
        apply Finset.card_eq_zero.2
        ext w
        simp only [Finset.notMem_empty, mem_neighborFinset, iff_false]
        intro hadj
        exact hI.1 (by rw [h]; trivial) (by rw [h]; trivial) hadj.ne hadj
      have hdegΔ : G.degree v = Δ := hreg' v
      omega
    let G' : SimpleGraph ↥(Iᶜ : Set V) := G.induce (Iᶜ : Set V)
    have : Nonempty ↥(Iᶜ : Set V) := hIc_nonempty.to_subtype
    have hΔ'lt : G'.maxDegree < Δ := by
      simpa [G', Δ] using maxDegree_induce_compl_lt_of_maximal (G := G) hI
    by_cases hEasy : G'.Colorable (Δ - 1)
    · have hcol := Colorable.of_induce_compl_isIndepSet hI.1 hEasy
      have : Δ - 1 + 1 = Δ := by omega
      exact this ▸ hcol
    · have hΔ'eq : G'.maxDegree = Δ - 1 := by
        have hle : G'.maxDegree ≤ Δ - 1 := Nat.le_sub_one_of_lt hΔ'lt
        refine le_antisymm hle ?_
        by_contra hlt
        push Not at hlt
        exact hEasy (Colorable.mono (by omega) G'.colorable_maxDegree_succ)
      have hcard' : Fintype.card ↥(Iᶜ : Set V) ≤ k := by
        have hsplit := Fintype.card_compl_set I
        have hIpos : 0 < Fintype.card ↥I := by
          rw [Fintype.card_pos_iff]; exact hI_nonempty.to_subtype
        omega
      have hnot : ¬ G'.Colorable G'.maxDegree := by simpa [hΔ'eq] using hEasy
      have hQcase :
          (¬ G'.CliqueFree Δ) ∨ (G'.maxDegree = 2 ∧ G'.HasOddCycle) := by
        by_cases hcf' : G'.CliqueFree (G'.maxDegree + 1)
        · by_cases hodd' : G'.maxDegree = 2 → ¬ G'.HasOddCycle
          · exact absurd (ih G' hcard' hcf' hodd') hnot
          · push Not at hodd'
            exact Or.inr hodd'
        · left
          have : G'.maxDegree + 1 = Δ := by omega
          simpa [this] using hcf'
      exact brooksSurgery (G := G) hΔdef hΔ3 hcf hH hreg' hI hΔ'eq hcard hcard' hQcase
        (fun {V} G => @ih V G)

/-- **Brooks' theorem** (Rabern's form). -/
theorem brooks (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (h : ¬ G.Colorable G.maxDegree) :
    ¬ G.CliqueFree (G.maxDegree + 1) ∨ (G.maxDegree = 2 ∧ G.HasOddCycle) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hcf, hodd⟩ := hcon
  exact h (brooksAux _ G le_rfl hcf fun h2 => (hodd h2).elim)

end SimpleGraph

end

namespace SimpleGraph

open Finset

/-- A maximum-degree-plus-one clique in a connected graph contains every vertex. -/
private theorem complete_of_connected_maximum_clique {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (C : Finset V) (hC : G.IsNClique (G.maxDegree + 1) C) : G = ⊤ := by
  classical
  have hclosed (x : V) (hx : x ∈ C) (y : V) (hxy : G.Adj x y) : y ∈ C := by
    have hsub : C.erase x ⊆ G.neighborFinset x := by
      intro z hz
      obtain ⟨hzx, hzC⟩ := Finset.mem_erase.mp hz
      exact (G.mem_neighborFinset x z).mpr (hC.isClique hx hzC hzx.symm)
    have hcard : (C.erase x).card = G.maxDegree := by
      rw [Finset.card_erase_of_mem hx, hC.card_eq]
      simp
    have heq : C.erase x = G.neighborFinset x :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [hcard, G.card_neighborFinset_eq_degree]
        exact G.degree_le_maxDegree x)
    have hy : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).mpr hxy
    rw [← heq] at hy
    exact (Finset.mem_erase.mp hy).2
  have hnonempty : C.Nonempty := Finset.card_pos.mp (by
    rw [hC.card_eq]
    exact Nat.succ_pos _)
  obtain ⟨v, hv⟩ := hnonempty
  have hall (x : V) : x ∈ C := by
    by_contra hx
    obtain ⟨p⟩ := hc v x
    obtain ⟨d, _, hd, hnd⟩ := p.exists_boundary_dart (C : Set V) hv hx
    exact hnd (hclosed d.fst hd d.snd d.adj)
  ext x y
  change G.Adj x y ↔ x ≠ y
  exact ⟨fun h => h.ne, hC.isClique (hall x) (hall y)⟩


/-- A cycle in a connected graph of maximum degree at most two is the whole graph. -/
private theorem eq_cycle_spanningCoe_of_connected_degree_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hd : G.maxDegree ≤ 2) {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    G = p.toSubgraph.spanningCoe ∧ ∀ x : V, x ∈ p.support := by
  classical
  have hdeg (x : V) : (G.neighborSet x).ncard ≤ 2 := by
    rw [Set.ncard_eq_toFinset_card', ← G.neighborFinset_def,
      G.card_neighborFinset_eq_degree]
    exact (G.degree_le_maxDegree x).trans hd
  have hneighbor (x : V) (hx : x ∈ p.toSubgraph.verts) :
      p.toSubgraph.neighborSet x = G.neighborSet x := by
    apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset x)
    rw [hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hx)]
    exact hdeg x
  have hclosed (x : V) (hx : x ∈ p.toSubgraph.verts) (y : V)
      (hxy : G.Adj x y) : y ∈ p.toSubgraph.verts := by
    apply p.toSubgraph.neighborSet_subset_verts x
    rw [hneighbor x hx]
    exact hxy
  have hall (x : V) : x ∈ p.toSubgraph.verts := by
    by_contra hx
    obtain ⟨q⟩ := hc u x
    obtain ⟨d, _, hd, hnd⟩ := q.exists_boundary_dart p.toSubgraph.verts
      p.start_mem_verts_toSubgraph hx
    exact hnd (hclosed d.fst hd d.snd d.adj)
  refine ⟨?_, fun x => p.mem_verts_toSubgraph.mp (hall x)⟩
  ext x y
  change G.Adj x y ↔ p.toSubgraph.Adj x y
  constructor
  · intro h
    change y ∈ p.toSubgraph.neighborSet x
    rw [hneighbor x (hall x)]
    exact h
  · exact p.toSubgraph.adj_sub


/-- A cycle in a finite connected graph of maximum degree at most two gives an actual
isomorphism with the cycle graph of its length. -/
private theorem cycle_iso_of_connected_degree_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hd : G.maxDegree ≤ 2) {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    Nonempty (cycleGraph p.length ≃g G) := by
  classical
  obtain ⟨heq, hspan⟩ := eq_cycle_spanningCoe_of_connected_degree_le_two G hc hd p hp
  have hcard : p.length = Fintype.card V := by
    have hs : p.support.toFinset = (univ : Finset V) := by
      ext x
      simp [hspan x]
    rw [← hp.support_toFinset_card, hs, card_univ]
  obtain ⟨f⟩ := (cycleGraph_isContained_iff hp.three_le_length).2 ⟨u, p, hp, rfl⟩
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨f.injective, by simpa using hcard⟩
  let e : Fin p.length ≃ V := Equiv.ofBijective f hbij
  have hdeg (x : Fin p.length) : (cycleGraph p.length).degree x = 2 := by
    have hn : p.length = (p.length - 3) + 3 := by have := hp.three_le_length; omega
    generalize p.length = n at x hn ⊢
    match n with
    | 0 | 1 | 2 => omega
    | k + 3 => exact cycleGraph_degree_three_le
  have hneigh (x : Fin p.length) :
      ((cycleGraph p.length).neighborFinset x).image f = G.neighborFinset (f x) := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
      exact (G.mem_neighborFinset _ _).2 (f.toHom.map_rel ((mem_neighborFinset _ _ _).1 hz))
    · rw [card_image_of_injective (f := (f : Fin p.length → V)) _ f.injective,
        G.card_neighborFinset_eq_degree,
        (cycleGraph p.length).card_neighborFinset_eq_degree, hdeg]
      exact (G.degree_le_maxDegree _).trans hd
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro x y
  change G.Adj (f x) (f y) ↔ (cycleGraph p.length).Adj x y
  refine ⟨?_, f.toHom.map_rel⟩
  intro h
  have hy : f y ∈ G.neighborFinset (f x) := (G.mem_neighborFinset _ _).2 h
  rw [← hneigh x] at hy
  obtain ⟨z, hz, hzy⟩ := mem_image.mp hy
  obtain rfl := f.injective hzy
  exact (mem_neighborFinset _ _ _).1 hz

/-- The complete connected Brooks alternative, with every noncomplete odd-cycle exception
represented by an actual cycle-graph isomorphism and length at least five. -/
theorem brooks_connected {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) :
    G.Colorable G.maxDegree ∨ G = ⊤ ∨
      ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ Nonempty (cycleGraph n ≃g G) := by
  classical
  by_cases hcol : G.Colorable G.maxDegree
  · exact Or.inl hcol
  rcases G.brooks hcol with hclique | ⟨hd, u, p, hp, hodd⟩
  · obtain ⟨C, hC⟩ := not_forall.mp hclique
    have hC' : G.IsNClique (G.maxDegree + 1) C := by simpa using hC
    exact Or.inr (Or.inl (complete_of_connected_maximum_clique G hc C hC'))
  · by_cases hthree : p.length = 3
    · obtain ⟨C, hC⟩ := is3Clique_iff_exists_cycle_length_three.2 ⟨u, p, hp, hthree⟩
      exact Or.inr (Or.inl (complete_of_connected_maximum_clique G hc C (by simpa [hd] using hC)))
    · refine Or.inr (Or.inr ⟨p.length, hodd, ?_, ?_⟩)
      · have := hp.three_le_length
        obtain ⟨k, hk⟩ := hodd
        omega
      · exact cycle_iso_of_connected_degree_le_two G hc (by omega) p hp

end SimpleGraph
