/- GID: D5/S3/Combinatorics/Graph/Brooks/CliqueExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Brooks/CliqueExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Color extensions across an almost-complete graph and a clique with prescribed outside neighbors. -/

import D5.S3.Combinatorics.Graph.Brooks.ColoringExtension
import Mathlib.Combinatorics.Hall.Finite

/-
Copyright (c) 2026 Brian Rabern. All rights reserved.
Released under Apache 2.0 license as described in
`docs/reports/brooks-suppliers/BrooksLean-LICENSE.txt`.
Authors: Brian Rabern and Opus 5

Source: https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d
Units: BrooksLean/OddCycle.lean, BrooksLean/VertexLemmas.lean, BrooksLean/Brooks.lean.
Modified from the retained General source by capacity partition on 2026-10-19.
Module framing, imports and consumed helper visibility are adapted here.
The induced-clique degree and connectedness helpers directly reuse pinned
Mathlib statements after rewriting the induced clique as the top graph.
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

/-! ### Auxiliary notions -/

/-- `K⁻ₙ₊₂`: the complete graph on `Fin (n + 2)` with the single edge `{0, 1}` removed.

So `K⁻_{k+1}` is `cliqueMinusEdge (k - 1)` for `k ≥ 3`. -/
def cliqueMinusEdge (n : ℕ) : SimpleGraph (Fin (n + 2)) :=
  (⊤ : SimpleGraph (Fin (n + 2))).deleteEdges {s(0, 1)}

private lemma cliqueMinusEdge_le_top (n : ℕ) :
    cliqueMinusEdge n ≤ (⊤ : SimpleGraph (Fin (n + 2))) :=
  deleteEdges_le _

private theorem cliqueFree_of_cliqueMinusEdge_free {k : ℕ}
    (h : ¬ cliqueMinusEdge k ⊑ G) : G.CliqueFree (k + 2) := by
  intro s hs
  exact h <| (IsContained.of_le (cliqueMinusEdge_le_top k)).trans <|
    not_cliqueFree_iff_top_isContained (k + 2) |>.1 fun hcf => hcf s hs

/-- An equivalence with `σ 0 = a` and `σ 1 = b`, assuming `a ≠ b`. -/
private def finPlaceTwo {n : ℕ} (a b : Fin (n + 2)) (_hne : a ≠ b) : Fin (n + 2) ≃ Fin (n + 2) :=
  (Equiv.swap 0 a).trans (Equiv.swap (Equiv.swap 0 a 1) b)

private lemma finPlaceTwo_zero {n : ℕ} (a b : Fin (n + 2)) (hne : a ≠ b) :
    finPlaceTwo a b hne 0 = a := by
  simp only [finPlaceTwo, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_def]
  split_ifs <;> simp_all

private lemma finPlaceTwo_one {n : ℕ} (a b : Fin (n + 2)) (hne : a ≠ b) :
    finPlaceTwo a b hne 1 = b := by
  simp [finPlaceTwo, Equiv.swap_apply_left]

/-- STEP 10: if `G` has no `K⁻_{k+2}`, then adding one edge cannot create a `K_{k+2}`. -/
private theorem cliqueFree_sup_edge_of_cliqueMinusEdge_free {k : ℕ} (u w : V)
    (h : ¬ cliqueMinusEdge k ⊑ G) :
    (G ⊔ edge u w).CliqueFree (k + 2) := by
  classical
  have hcf : G.CliqueFree (k + 2) := cliqueFree_of_cliqueMinusEdge_free h
  by_cases hne : u = w
  · subst hne; simpa [sup_edge_self] using hcf
  by_cases hadj : G.Adj u w
  · simpa [sup_edge_of_adj G hadj] using hcf
  intro s hs
  have hu : u ∈ s := hcf.mem_of_sup_edge_isNClique hs
  have hw : w ∈ s := by
    have hs' : (G ⊔ edge w u).IsNClique (k + 2) s := by rwa [edge_comm]
    exact hcf.mem_of_sup_edge_isNClique hs'
  let e : Fin (k + 2) ≃ ↥s := (Finset.equivFinOfCardEq (s := s) hs.card_eq).symm
  let a : Fin (k + 2) := e.symm ⟨u, hu⟩
  let b : Fin (k + 2) := e.symm ⟨w, hw⟩
  have hab : a ≠ b := fun hEq => hne (by
    have := congrArg (fun i => (e i : V)) hEq
    simpa [a, b] using this)
  let σ := finPlaceTwo a b hab
  have hσ0 : σ 0 = a := finPlaceTwo_zero a b hab
  have hσ1 : σ 1 = b := finPlaceTwo_one a b hab
  let f : Fin (k + 2) → V := fun i => ↑(e (σ i))
  have hinj : Function.Injective f := by
    intro x y hxy
    exact σ.injective (e.injective (Subtype.ext hxy))
  have hf0 : f 0 = u := by simp [f, hσ0, a]
  have hf1 : f 1 = w := by simp [f, hσ1, b]
  have hhom : ∀ {x y : Fin (k + 2)}, (cliqueMinusEdge k).Adj x y → G.Adj (f x) (f y) := by
    intro x y hxy
    have hxy' : x ≠ y ∧ s(x, y) ≠ s(0, 1) := by
      simpa [cliqueMinusEdge, deleteEdges_adj, top_adj] using hxy
    have hadjSup : (G ⊔ edge u w).Adj (f x) (f y) := by
      refine hs.isClique (e (σ x)).property (e (σ y)).property ?_
      exact fun hEq => hxy'.1 (hinj hEq)
    rw [sup_adj, edge_adj] at hadjSup
    rcases hadjSup with hG | ⟨hpair, _⟩
    · exact hG
    · have : s(f x, f y) = s(u, w) := by
        rcases hpair with ⟨hxu, hyw⟩ | ⟨hxw, hyu⟩
        · simp [hxu, hyw]
        · rw [hxw, hyu, Sym2.eq_swap]
      have hmap : Sym2.map f s(x, y) = Sym2.map f s(0, 1) := by
        simpa [Sym2.map_mk, hf0, hf1] using this
      have hinj2 : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
      exact absurd (hinj2 hmap) hxy'.2
  exact absurd ⟨Hom.toCopy ⟨f, fun {_ _} => hhom⟩ hinj⟩ h

/-! ### The `K⁻` extension (STEP 2) -/

section CliqueMinusEdgeColorable
open Classical

private lemma neighborFinset_cliqueMinusEdge_zero (n : ℕ) :
    (cliqueMinusEdge n).neighborFinset (0 : Fin (n + 2)) = (Finset.univ.erase 0).erase 1 := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    have hadj : (cliqueMinusEdge n).Adj 0 i := (mem_neighborFinset _ _ _).1 hi
    have h := deleteEdges_adj.1 hadj
    have hine : i ≠ 0 := h.1.ne'
    have hine01 : s((0 : Fin (n + 2)), i) ≠ s(0, 1) := by
      simpa [Set.mem_singleton_iff] using h.2
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨hine, Finset.mem_univ _⟩⟩
    intro h1; exact hine01 (h1 ▸ rfl)
  · intro hi
    have hi1 : i ≠ 1 := (Finset.mem_erase.1 hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    apply (mem_neighborFinset _ _ _).2
    refine deleteEdges_adj.2 ⟨(top_adj 0 i).2 hi0.symm, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hEq
    rcases Sym2.eq_iff.mp hEq with ⟨_, rfl⟩ | ⟨h01, _⟩
    · exact hi1 rfl
    · exact Fin.zero_ne_one h01

private lemma degree_cliqueMinusEdge_zero (n : ℕ) :
    (cliqueMinusEdge n).degree (0 : Fin (n + 2)) = n := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_cliqueMinusEdge_zero,
    Finset.card_erase_of_mem (by simp [Fin.zero_ne_one.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

private lemma neighborFinset_cliqueMinusEdge_one (n : ℕ) :
    (cliqueMinusEdge n).neighborFinset (1 : Fin (n + 2)) = (Finset.univ.erase 0).erase 1 := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    have hadj : (cliqueMinusEdge n).Adj 1 i := (mem_neighborFinset _ _ _).1 hi
    have h := deleteEdges_adj.1 hadj
    have hine : i ≠ 1 := h.1.ne'
    have hine01 : s((1 : Fin (n + 2)), i) ≠ s(0, 1) := by
      simpa [Set.mem_singleton_iff] using h.2
    refine Finset.mem_erase.2 ⟨hine, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩⟩
    intro h0; subst h0; exact hine01 (by rw [Sym2.eq_swap])
  · intro hi
    have hi1 : i ≠ 1 := (Finset.mem_erase.1 hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    apply (mem_neighborFinset _ _ _).2
    refine deleteEdges_adj.2 ⟨(top_adj 1 i).2 hi1.symm, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hEq
    rcases Sym2.eq_iff.mp hEq with ⟨h10, _⟩ | ⟨_, hi0'⟩
    · exact Fin.zero_ne_one h10.symm
    · exact hi0 hi0'

private lemma degree_cliqueMinusEdge_one (n : ℕ) :
    (cliqueMinusEdge n).degree (1 : Fin (n + 2)) = n := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_cliqueMinusEdge_one,
    Finset.card_erase_of_mem (by simp [Fin.zero_ne_one.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

private lemma degree_cliqueMinusEdge_of_ne_zero_one {n : ℕ} {i : Fin (n + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    (cliqueMinusEdge n).degree i = n + 1 := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (cliqueMinusEdge n).neighborFinset i = Finset.univ.erase i := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      exact Finset.mem_erase.2 ⟨((mem_neighborFinset _ _ _).1 hj).ne', Finset.mem_univ _⟩
    · intro hj
      have hji : j ≠ i := (Finset.mem_erase.1 hj).1
      apply (mem_neighborFinset _ _ _).2
      refine deleteEdges_adj.2 ⟨(top_adj i j).2 hji.symm, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hEq
      rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hi0 rfl
      · exact hi1 rfl
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

private lemma map_neighborFinset_cliqueMinusEdge_subset
    {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {n : ℕ}
    (φ : Copy (cliqueMinusEdge n) G) (a : Fin (n + 2)) :
    ((cliqueMinusEdge n).neighborFinset a).map φ.toEmbedding ⊆
      G.neighborFinset (φ a) ∩ (Set.range φ).toFinset := by
  intro x hx
  rcases Finset.mem_map.1 hx with ⟨i, hi, rfl⟩
  refine Finset.mem_inter.2 ⟨?_, ?_⟩
  · exact (mem_neighborFinset _ _ _).2 (φ.toHom.map_adj ((mem_neighborFinset _ _ _).1 hi))
  · exact Set.mem_toFinset.2 ⟨i, rfl⟩

private lemma card_neighborFinset_sdiff_range_cliqueMinusEdge_le
    {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {n : ℕ} (hΔ : G.maxDegree ≤ n + 1) (φ : Copy (cliqueMinusEdge n) G)
    (a : Fin (n + 2)) (hdegH : (cliqueMinusEdge n).degree a = n) :
    (G.neighborFinset (φ a) \ (Set.range φ).toFinset).card ≤ 1 := by
  have hge : n ≤ (G.neighborFinset (φ a) ∩ (Set.range φ).toFinset).card := by
    have := Finset.card_le_card (map_neighborFinset_cliqueMinusEdge_subset φ a)
    rwa [Finset.card_map, card_neighborFinset_eq_degree, hdegH] at this
  have hsum :
      (G.neighborFinset (φ a) ∩ (Set.range φ).toFinset).card +
        (G.neighborFinset (φ a) \ (Set.range φ).toFinset).card =
        G.degree (φ a) := by
    rw [← card_neighborFinset_eq_degree, add_comm, Finset.card_sdiff_add_card_inter]
  have hdegG := (G.degree_le_maxDegree (φ a)).trans hΔ
  omega

private lemma neighborFinset_subset_range_of_degree_cliqueMinusEdge
    {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {n : ℕ} (hΔ : G.maxDegree ≤ n + 1) (φ : Copy (cliqueMinusEdge n) G)
    {i : Fin (n + 2)} (hdegH : (cliqueMinusEdge n).degree i = n + 1) :
    G.neighborFinset (φ i) ⊆ (Set.range φ).toFinset := by
  intro w hw
  by_contra hwn
  have hge : n + 1 ≤ (G.neighborFinset (φ i) ∩ (Set.range φ).toFinset).card := by
    have := Finset.card_le_card (map_neighborFinset_cliqueMinusEdge_subset φ i)
    rwa [Finset.card_map, card_neighborFinset_eq_degree, hdegH] at this
  have hsum :
      (G.neighborFinset (φ i) ∩ (Set.range φ).toFinset).card +
        (G.neighborFinset (φ i) \ (Set.range φ).toFinset).card =
        G.degree (φ i) := by
    rw [← card_neighborFinset_eq_degree, add_comm, Finset.card_sdiff_add_card_inter]
  have hdegG := (G.degree_le_maxDegree (φ i)).trans hΔ
  have hpos : (G.neighborFinset (φ i) \ (Set.range φ).toFinset).card ≥ 1 :=
    Finset.one_le_card.2 ⟨w, Finset.mem_sdiff.2 ⟨hw, hwn⟩⟩
  omega

private lemma not_adj_ends_of_cliqueMinusEdge_copy
    {V : Type u} {G : SimpleGraph V} {n : ℕ} (hcf : G.CliqueFree (n + 1))
    (hn : 1 ≤ n) (φ : Copy (cliqueMinusEdge (n - 1)) G) :
    ¬ G.Adj (φ 0) (φ 1) := by
  intro hadj
  have hsz : n - 1 + 2 = n + 1 := by omega
  have htop : (⊤ : SimpleGraph (Fin (n - 1 + 2))) ⊑ G := by
    refine ⟨Hom.toCopy ⟨φ, fun {a b} hab => ?_⟩ φ.injective⟩
    by_cases hab01 : s(a, b) = s((0 : Fin (n - 1 + 2)), 1)
    · have hφ : s(φ a, φ b) = s(φ 0, φ 1) := by
        rcases Sym2.eq_iff.mp hab01 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · simp [ha, hb]
        · simp [ha, hb, Sym2.eq_swap]
      rcases Sym2.eq_iff.mp hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1 ▸ h2 ▸ hadj
      · exact h1 ▸ h2 ▸ hadj.symm
    · exact φ.toHom.map_adj <| by
        simp only [cliqueMinusEdge, deleteEdges_adj, top_adj, Set.mem_singleton_iff]
        exact ⟨hab.ne, hab01⟩
  exact (not_cliqueFree_iff_top_isContained (n + 1)).2 (by rwa [← hsz]) hcf

/-- If `G` contains a copy of `K⁻_{n+1}` and the complement of its image is `n`-colourable, then
`G` is `n`-colourable (Rabern STEP 2). -/
theorem Colorable.of_cliqueMinusEdge_copy {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    {n : ℕ} (hn : 3 ≤ n) (hΔ : G.maxDegree ≤ n) (hcf : G.CliqueFree (n + 1))
    (φ : Copy (cliqueMinusEdge (n - 1)) G)
    (hcol : (G.induce ((Set.range φ)ᶜ : Set V)).Colorable n) :
    G.Colorable n := by
  have : NeZero n := ⟨by lia⟩
  obtain ⟨C⟩ := hcol
  let S : Set V := Set.range φ
  let x : V := φ 0
  let y : V := φ 1
  have hnotAdj : ¬ G.Adj x y := not_adj_ends_of_cliqueMinusEdge_copy hcf (by lia) φ
  have hx_out : (G.neighborFinset x \ S.toFinset).card ≤ 1 := by
    simpa [x, S] using card_neighborFinset_sdiff_range_cliqueMinusEdge_le
      (n := n - 1) (by omega) φ 0 (degree_cliqueMinusEdge_zero _)
  have hy_out : (G.neighborFinset y \ S.toFinset).card ≤ 1 := by
    simpa [y, S] using card_neighborFinset_sdiff_range_cliqueMinusEdge_le
      (n := n - 1) (by omega) φ 1 (degree_cliqueMinusEdge_one _)
  let fOut : V → Fin n := fun v => if hv : v ∈ Sᶜ then C ⟨v, hv⟩ else 0
  let Nx : Finset V := G.neighborFinset x \ S.toFinset
  let Ny : Finset V := G.neighborFinset y \ S.toFinset
  have hNx : Nx.card ≤ 1 := hx_out
  have hNy : Ny.card ≤ 1 := hy_out
  obtain ⟨α, hα⟩ : ∃ α : Fin n, α ∉ (Nx ∪ Ny).image fOut := by
    have hcard : ((Nx ∪ Ny).image fOut).card ≤ 2 :=
      (Finset.card_image_le).trans ((Finset.card_union_le _ _).trans (by omega))
    obtain ⟨α, hα⟩ : (((Nx ∪ Ny).image fOut)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      omega
    exact ⟨α, Finset.mem_compl.1 hα⟩
  have hαx : ∀ v ∈ Nx, fOut v ≠ α := fun v hv hEq =>
    hα (hEq ▸ Finset.mem_image_of_mem fOut (Finset.mem_union_left _ hv))
  have hαy : ∀ v ∈ Ny, fOut v ≠ α := fun v hv hEq =>
    hα (hEq ▸ Finset.mem_image_of_mem fOut (Finset.mem_union_right _ hv))
  let ψ : Fin (n - 1 + 2) ≃ ↥S := Equiv.ofInjective (↑φ) φ.injective
  let rest : Finset (Fin (n - 1 + 2)) := (Finset.univ.erase 0).erase 1
  have hrest_card : rest.card = n - 1 := by
    simp [rest, Finset.card_erase_of_mem, Finset.mem_univ, Fin.zero_ne_one.symm,
      Finset.card_univ, Fintype.card_fin]
  let colors : Finset (Fin n) := Finset.univ.erase α
  have hcolors_card : colors.card = n - 1 := by
    simp [colors, Finset.card_erase_of_mem, Finset.mem_univ, Fintype.card_fin]
  let e : ↥rest ≃ ↥colors := Finset.equivOfCardEq (hrest_card.trans hcolors_card.symm)
  let colorH : Fin (n - 1 + 2) → Fin n := fun i =>
    if h : i ∈ rest then (e ⟨i, h⟩).1 else α
  have colorH_end {i : Fin (n - 1 + 2)} (hi : i ∉ rest) : colorH i = α := by
    simp [colorH, hi]
  have colorH_rest {i : Fin (n - 1 + 2)} (hi : i ∈ rest) : colorH i = (e ⟨i, hi⟩).1 := by
    simp [colorH, hi]
  have mem_rest_iff {i : Fin (n - 1 + 2)} : i ∈ rest ↔ i ≠ 0 ∧ i ≠ 1 := by
    simp [rest, Finset.mem_erase, Finset.mem_univ, and_comm]
  have φ_symm (v : V) (hv : v ∈ S) : φ (ψ.symm ⟨v, hv⟩) = v :=
    congrArg Subtype.val (ψ.apply_symm_apply ⟨v, hv⟩)
  let color : V → Fin n := fun v =>
    if hv : v ∈ S then colorH (ψ.symm ⟨v, hv⟩) else C ⟨v, hv⟩
  refine ⟨Coloring.mk color ?_⟩
  intro u v huv
  dsimp [color]
  by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
  · -- both in the copy
    simp only [huS, hvS, ↓reduceDIte]
    set i := ψ.symm ⟨u, huS⟩
    set j := ψ.symm ⟨v, hvS⟩
    have hui : φ i = u := φ_symm u huS
    have hvj : φ j = v := φ_symm v hvS
    have hij : i ≠ j := fun hEq => huv.ne (by rw [← hui, ← hvj, hEq])
    by_cases hi : i ∈ rest <;> by_cases hj : j ∈ rest
    · rw [colorH_rest hi, colorH_rest hj]
      exact Subtype.coe_injective.ne (e.injective.ne (Subtype.ext_iff.not.mpr hij))
    · rw [colorH_rest hi, colorH_end hj]
      exact Finset.ne_of_mem_erase (e ⟨i, hi⟩).property
    · rw [colorH_end hi, colorH_rest hj]
      exact (Finset.ne_of_mem_erase (e ⟨j, hj⟩).property).symm
    · -- both ends: must be `{0,1}`, which are non-adjacent
      have hi01 : i = 0 ∨ i = 1 := by
        have := (mem_rest_iff (i := i)).not.1 hi
        push Not at this; tauto
      have hj01 : j = 0 ∨ j = 1 := by
        have := (mem_rest_iff (i := j)).not.1 hj
        push Not at this; tauto
      have : ¬ G.Adj (φ i) (φ j) := by
        rcases hi01 with hi0 | hi0 <;> rcases hj01 with hj0 | hj0
        · exact absurd (hi0.trans hj0.symm) hij
        · simpa [x, y, hui, hvj, hi0, hj0] using hnotAdj
        · simpa [x, y, hui, hvj, hi0, hj0, adj_comm] using hnotAdj
        · exact absurd (hi0.trans hj0.symm) hij
      exact absurd (by simpa [hui, hvj] using huv) this
  · -- `u` in copy, `v` outside
    simp only [huS, hvS, ↓reduceDIte]
    set i := ψ.symm ⟨u, huS⟩
    have hui : φ i = u := φ_symm u huS
    by_cases hi : i ∈ rest
    · -- rest vertices have no outside neighbours
      have hi01 : i ≠ 0 ∧ i ≠ 1 := (mem_rest_iff (i := i)).1 hi
      have hdeg : (cliqueMinusEdge (n - 1)).degree i = (n - 1) + 1 :=
        degree_cliqueMinusEdge_of_ne_zero_one (n := n - 1) hi01.1 hi01.2
      have hN : G.neighborFinset (φ i) ⊆ S.toFinset := by
        simpa [S] using neighborFinset_subset_range_of_degree_cliqueMinusEdge
          (n := n - 1) (by omega) φ hdeg
      exact absurd (Set.mem_toFinset.1 (hN (by simpa [hui] using (mem_neighborFinset _ _ _).2 huv)))
        (mt Set.mem_toFinset.2 (by simpa [Set.mem_toFinset] using hvS))
    · rw [colorH_end hi]
      have hi01 : i = 0 ∨ i = 1 := by
        have := (mem_rest_iff (i := i)).not.1 hi
        push Not at this; tauto
      have huxy : u = x ∨ u = y :=
        hi01.imp (fun h => hui.symm.trans (congrArg φ h)) (fun h => hui.symm.trans (congrArg φ h))
      have hfOut : fOut v = C ⟨v, hvS⟩ := dif_pos hvS
      rcases huxy with rfl | rfl
      · exact (hfOut ▸ hαx v (Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 huv,
          fun h => hvS (Set.mem_toFinset.1 h)⟩)).symm
      · exact (hfOut ▸ hαy v (Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 huv,
          fun h => hvS (Set.mem_toFinset.1 h)⟩)).symm
  · -- `u` outside, `v` in copy (symmetric)
    simp only [huS, hvS, ↓reduceDIte]
    set j := ψ.symm ⟨v, hvS⟩
    have hvj : φ j = v := φ_symm v hvS
    by_cases hj : j ∈ rest
    · have hj01 : j ≠ 0 ∧ j ≠ 1 := (mem_rest_iff (i := j)).1 hj
      have hdeg : (cliqueMinusEdge (n - 1)).degree j = (n - 1) + 1 :=
        degree_cliqueMinusEdge_of_ne_zero_one (n := n - 1) hj01.1 hj01.2
      have hN : G.neighborFinset (φ j) ⊆ S.toFinset := by
        simpa [S] using neighborFinset_subset_range_of_degree_cliqueMinusEdge
          (n := n - 1) (by omega) φ hdeg
      exact absurd (Set.mem_toFinset.1 (hN (by simpa [hvj] using (mem_neighborFinset _ _ _).2 huv.symm)))
        (mt Set.mem_toFinset.2 (by simpa [Set.mem_toFinset] using huS))
    · rw [colorH_end hj]
      have hj01 : j = 0 ∨ j = 1 := by
        have := (mem_rest_iff (i := j)).not.1 hj
        push Not at this; tauto
      have hvxy : v = x ∨ v = y :=
        hj01.imp (fun h => hvj.symm.trans (congrArg φ h)) (fun h => hvj.symm.trans (congrArg φ h))
      have hfOut : fOut u = C ⟨u, huS⟩ := dif_pos huS
      rcases hvxy with rfl | rfl
      · exact hfOut ▸ hαx u (Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 huv.symm,
          fun h => huS (Set.mem_toFinset.1 h)⟩)
      · exact hfOut ▸ hαy u (Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 huv.symm,
          fun h => huS (Set.mem_toFinset.1 h)⟩)
  · -- both outside
    simp only [huS, hvS, ↓reduceDIte]
    exact C.valid huv

end CliqueMinusEdgeColorable

/-! ### The induction -/

/-! ### Surgery helpers -/

/-- If a `Δ`-set `Q` is a clique of neighbours of `w`, then `Q ∪ {w}` is a `(Δ+1)`-clique. -/
private theorem isNClique_union_singleton_of_neighbors [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {Δ : ℕ} {Q : Finset V} {w : V}
    (hQcard : Q.card = Δ)
    (hQclique : G.IsClique (Q : Set V))
    (hwQ : w ∉ Q)
    (hN : G.neighborFinset w = Q) :
    G.IsNClique (Δ + 1) (Q ∪ {w}) := by
  refine ⟨?clique, ?card⟩
  case card =>
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hwQ),
      Finset.card_singleton, hQcard]
  case clique =>
    intro a ha b hb hne
    have ha' : a ∈ Q ∨ a = w := by
      have := Finset.mem_union.1 (show a ∈ Q ∪ {w} from ha)
      exact this.imp_right Finset.mem_singleton.1
    have hb' : b ∈ Q ∨ b = w := by
      have := Finset.mem_union.1 (show b ∈ Q ∪ {w} from hb)
      exact this.imp_right Finset.mem_singleton.1
    match ha', hb' with
    | Or.inl haQ, Or.inl hbQ =>
      exact hQclique (show a ∈ (Q : Set V) from haQ) (show b ∈ (Q : Set V) from hbQ) hne
    | Or.inl haQ, Or.inr hbw =>
      have : a ∈ G.neighborFinset w := by rw [hN]; exact haQ
      exact hbw ▸ ((mem_neighborFinset _ _ _).1 this).symm
    | Or.inr haw, Or.inl hbQ =>
      have : b ∈ G.neighborFinset w := by rw [hN]; exact hbQ
      exact haw ▸ (mem_neighborFinset _ _ _).1 this
    | Or.inr haw, Or.inr hbw =>
      exact (hne (haw.trans hbw.symm)).elim

/-- Neighbour set of `w` equals `Q` when `Q ⊆ N(w)` and both have cardinality `Δ`. -/
private theorem neighborFinset_eq_of_subset_of_card [Fintype V] [DecidableRel G.Adj]
    {Q : Finset V} {w : V} {Δ : ℕ}
    (hsub : Q ⊆ G.neighborFinset w)
    (hQcard : Q.card = Δ)
    (hdeg : G.degree w = Δ) :
    G.neighborFinset w = Q :=
  (Finset.eq_of_subset_of_card_le hsub
    (by rw [card_neighborFinset_eq_degree, hdeg, hQcard])).symm

/-- A complete graph on `n` vertices admits an `n`-colouring avoiding one forbidden colour
per vertex, provided the forbidden colours are not all equal. -/
private theorem exists_coloring_avoiding_of_isClique [Fintype V] [DecidableEq V]
    {n : ℕ} {s : Finset V} (_hs : G.IsClique (s : Set V)) (hcard : s.card = n)
    (f : V → Fin n) (hne : ∃ a ∈ s, ∃ b ∈ s, f a ≠ f b) :
    ∃ c : V → Fin n, (∀ a ∈ s, ∀ b ∈ s, a ≠ b → c a ≠ c b) ∧ ∀ a ∈ s, c a ≠ f a := by
  classical
  have hnpos : 0 < n := by
    obtain ⟨a, ha, b, hb, hab⟩ := hne
    have hab_ne : a ≠ b := fun h => hab (h ▸ rfl)
    have hle : ({a, b} : Finset V).card ≤ n := by
      rw [← hcard]
      exact Finset.card_le_card (Finset.insert_subset ha (Finset.singleton_subset_iff.2 hb))
    have h2 : ({a, b} : Finset V).card = 2 := by simp [Finset.card_insert_of_notMem, hab_ne]
    omega
  let ι := ↥s
  have hιcard : Fintype.card ι = n := by simp [ι, ← hcard]
  let t : ι → Finset (Fin n) := fun x => Finset.univ.erase (f x.1)
  have hcompl_mem (u : Finset ι) (c : Fin n) :
      c ∈ (u.biUnion t)ᶜ ↔ ∀ x ∈ u, f x.1 = c := by
    constructor
    · intro hc x hx
      have : c ∉ t x := fun htx =>
        (Finset.mem_compl.1 hc) (Finset.mem_biUnion.2 ⟨x, hx, htx⟩)
      exact (by simpa [t, Finset.mem_erase] using this : c = f x.1).symm
    · intro hc
      refine Finset.mem_compl.2 ?_
      intro hbi
      rcases Finset.mem_biUnion.1 hbi with ⟨x, hx, htx⟩
      have : c ≠ f x.1 := by simpa [t, Finset.mem_erase] using htx
      exact this (hc x hx).symm
  have hhall : ∀ (u : Finset ι), u.card ≤ (u.biUnion t).card := by
    intro u
    have hcard_b : (u.biUnion t).card = n - (u.biUnion t)ᶜ.card := by
      have := Finset.card_add_card_compl (u.biUnion t)
      simp only [Fintype.card_fin] at this
      omega
    by_cases he : u = ∅
    · subst he; simp
    · by_cases hcst : ∃ c : Fin n, ∀ x ∈ u, f x.1 = c
      · obtain ⟨c, hc⟩ := hcst
        have hcompl_eq : (u.biUnion t)ᶜ = {c} := by
          ext d
          rw [hcompl_mem, Finset.mem_singleton]
          constructor
          · intro hd
            obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty he
            exact (hd x hx).symm.trans (hc x hx)
          · intro hd x hx; exact hd ▸ hc x hx
        have hu_le : u.card ≤ n - 1 := by
          have hle_univ : u.card ≤ n := by simpa [hιcard] using Finset.card_le_univ u
          by_contra hgt
          have hu_eq : u.card = n := by omega
          have hu_univ : u = Finset.univ :=
            Finset.eq_univ_of_card u (by simp [hu_eq, hιcard])
          obtain ⟨a, ha, b, hb, hab⟩ := hne
          have : f a = f b := by
            have ha' : (⟨a, ha⟩ : ι) ∈ u := by simp [hu_univ]
            have hb' : (⟨b, hb⟩ : ι) ∈ u := by simp [hu_univ]
            exact (hc _ ha').trans (hc _ hb').symm
          exact hab this
        rw [hcard_b, hcompl_eq, Finset.card_singleton]
        omega
      · push Not at hcst
        have hcompl_empty : (u.biUnion t)ᶜ = ∅ := by
          ext c
          simp only [Finset.notMem_empty, hcompl_mem, iff_false]
          intro hc
          obtain ⟨x, hx, hne⟩ := hcst c
          exact hne (hc x hx)
        rw [hcard_b, hcompl_empty, Finset.card_empty, tsub_zero]
        simpa [hιcard] using Finset.card_le_univ u
  obtain ⟨g, hg_inj, hg_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).1 hhall
  refine ⟨fun v => if hv : v ∈ s then g ⟨v, hv⟩ else ⟨0, hnpos⟩, ?_, ?_⟩
  · intro a ha b hb hne'
    simp only [ha, hb, ↓reduceDIte]
    exact fun h => hne' (Subtype.ext_iff.1 (hg_inj h))
  · intro a ha
    simp only [ha, ↓reduceDIte]
    have := hg_mem ⟨a, ha⟩
    simpa [t, Finset.mem_erase] using this

/-- The unique neighbour of `v ∈ Q` outside `Q` is its star in `I`. -/
theorem eq_star_of_adj_mem_compl [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {Δ : ℕ} {I Q : Set V} [DecidablePred (· ∈ Q)]
    (hreg : G.IsRegularOfDegree Δ) (hk : 1 ≤ Δ)
    (hQI : Q ⊆ Iᶜ)
    (hQreg : (G.induce Q).IsRegularOfDegree (Δ - 1))
    {v : V} (hv : v ∈ Q) {w : V} (hw : w ∈ (Qᶜ : Set V)) (hadj : G.Adj v w)
    {ystar : V} (hystar : ystar ∈ I ∧ G.Adj v ystar) :
    w = ystar := by
  have hinter : (G.neighborFinset v ∩ Q.toFinset).card = Δ - 1 := by
    have hdegQ : (G.induce Q).degree ⟨v, hv⟩ = Δ - 1 := hQreg _
    have hmap := congrArg Finset.card (G.map_neighborFinset_induce (s := Q) ⟨v, hv⟩)
    simpa [card_neighborFinset_eq_degree, hdegQ] using hmap.symm
  have hsum :
      (G.neighborFinset v ∩ Q.toFinset).card + (G.neighborFinset v \ Q.toFinset).card =
        G.degree v := by
    rw [← card_neighborFinset_eq_degree, add_comm, Finset.card_sdiff_add_card_inter]
  have hout : (G.neighborFinset v \ Q.toFinset).card = 1 := by
    have hdeg := hreg v
    have h : (Δ - 1) + (G.neighborFinset v \ Q.toFinset).card = Δ := by
      rw [← hinter, ← hdeg]; exact hsum
    omega
  obtain ⟨w0, hw0⟩ := Finset.card_eq_one.1 hout
  have hwout : w ∈ G.neighborFinset v \ Q.toFinset :=
    Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 hadj, by
      simp [Set.mem_toFinset]; exact hw⟩
  have hstar_out : ystar ∈ G.neighborFinset v \ Q.toFinset := by
    refine Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 hystar.2, ?_⟩
    simp only [Set.mem_toFinset]
    exact fun hQ => absurd hystar.1 (Set.notMem_of_mem_compl (hQI hQ))
  have hw_eq : w = w0 := by rw [hw0] at hwout; simpa using hwout
  have hs_eq : ystar = w0 := by rw [hw0] at hstar_out; simpa using hstar_out
  exact hw_eq.trans hs_eq.symm

/-- If every vertex of a `Δ`-clique `Q ⊆ Iᶜ` stars at the same `w ∈ I`, we get a `K_{Δ+1}`. -/
theorem isNClique_of_const_star [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {Δ : ℕ} {I : Set V} {Q : Finset V} {w : V}
    (hQcard : Q.card = Δ) (hQclique : G.IsClique (Q : Set V))
    (hQI : ↑Q ⊆ (Iᶜ : Set V)) (hwI : w ∈ I)
    (hadj : ∀ v ∈ Q, G.Adj v w) (hreg : G.degree w = Δ) :
    G.IsNClique (Δ + 1) (Q ∪ {w}) := by
  have hwQ : w ∉ Q := fun h => absurd hwI (Set.notMem_of_mem_compl (hQI h))
  have hsub : Q ⊆ G.neighborFinset w := fun v hv =>
    (mem_neighborFinset _ _ _).2 (hadj v hv).symm
  exact isNClique_union_singleton_of_neighbors hQcard hQclique hwQ
    (neighborFinset_eq_of_subset_of_card hsub hQcard hreg)

/-- Combine a colouring of `Qᶜ` with a Hall colouring of the clique `Q` that avoids star colours. -/
theorem Colorable.of_clique_block_with_stars [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {n : ℕ} {Q : Set V} [DecidablePred (· ∈ Q)] {I : Set V}
    (hQclique : G.IsClique Q) (hQcard : Q.ncard = n)
    (hQI : Q ⊆ (Iᶜ : Set V))
    (C : (G.induce (Qᶜ : Set V)).Coloring (Fin n))
    (star : V → V)
    (hstar : ∀ v ∈ Q, star v ∈ I ∧ G.Adj v (star v))
    (honly : ∀ v ∈ Q, ∀ w, w ∈ (Qᶜ : Set V) → G.Adj v w → w = star v)
    {a b : V} (ha : a ∈ Q) (hb : b ∈ Q)
    (hneC : C ⟨star a, fun h => absurd (hstar a ha).1 (Set.notMem_of_mem_compl (hQI h))⟩ ≠
            C ⟨star b, fun h => absurd (hstar b hb).1 (Set.notMem_of_mem_compl (hQI h))⟩) :
    G.Colorable n := by
  classical
  let Qf : Finset V := Q.toFinset
  have hQf_coe : (Qf : Set V) = Q := Set.coe_toFinset _
  have hQf_card : Qf.card = n := by rw [← Set.ncard_eq_toFinset_card' Q, hQcard]
  have hstar_Qc (v : V) (hv : v ∈ Q) : star v ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar v hv).1 (Set.notMem_of_mem_compl (hQI h))
  have hnpos : 0 < n := by
    have hab_ne : a ≠ b := fun heq => by
      subst heq
      exact hneC rfl
    have h2 : ({a, b} : Finset V).card = 2 := by
      simp [Finset.card_insert_of_notMem, hab_ne]
    have hle : ({a, b} : Finset V).card ≤ n := by
      rw [← hQf_card]
      exact Finset.card_le_card
        (Finset.insert_subset (by simpa [← Set.mem_toFinset] using ha)
          (Finset.singleton_subset_iff.2 (by simpa [← Set.mem_toFinset] using hb)))
    omega
  let f : V → Fin n := fun v =>
    if hv : v ∈ Q then C ⟨star v, hstar_Qc v hv⟩ else ⟨0, hnpos⟩
  have hne_f : ∃ x ∈ Qf, ∃ y ∈ Qf, f x ≠ f y :=
    ⟨a, by simpa [← Set.mem_toFinset] using ha, b, by simpa [← Set.mem_toFinset] using hb,
      by simpa [f, ha, hb] using hneC⟩
  obtain ⟨cQ, hcQ_proper, hcQ_avoid⟩ :=
    exists_coloring_avoiding_of_isClique (by simpa [hQf_coe] using hQclique) hQf_card f hne_f
  let color : V → Fin n := fun v => if hv : v ∈ Q then cQ v else C ⟨v, Set.mem_compl hv⟩
  refine ⟨Coloring.mk color fun {x y} hxy => ?_⟩
  dsimp [color]
  by_cases hxQ : x ∈ Q <;> by_cases hyQ : y ∈ Q
  · have hxQf : x ∈ Qf := by simpa [← Set.mem_toFinset] using hxQ
    have hyQf : y ∈ Qf := by simpa [← Set.mem_toFinset] using hyQ
    simpa [hxQ, hyQ] using hcQ_proper x hxQf y hyQf hxy.ne
  · have hyQc : y ∈ (Qᶜ : Set V) := Set.mem_compl hyQ
    have hy_eq : y = star x := honly x hxQ y hyQc hxy
    have hxQf : x ∈ Qf := by simpa [← Set.mem_toFinset] using hxQ
    have havoid := hcQ_avoid x hxQf
    simp only [f, hxQ, ↓reduceDIte] at havoid
    rw [hy_eq]
    simp only [hxQ, show star x ∉ Q from hy_eq ▸ hyQ, ↓reduceDIte]
    exact havoid
  · have hxQc : x ∈ (Qᶜ : Set V) := Set.mem_compl hxQ
    have hx_eq : x = star y := honly y hyQ x hxQc hxy.symm
    have hyQf : y ∈ Qf := by simpa [← Set.mem_toFinset] using hyQ
    have havoid := hcQ_avoid y hyQf
    simp only [f, hyQ, ↓reduceDIte] at havoid
    rw [hx_eq]
    simp only [hyQ, show star y ∉ Q from hx_eq ▸ hxQ, ↓reduceDIte]
    exact havoid.symm
  · have hxQc : x ∈ (Qᶜ : Set V) := Set.mem_compl hxQ
    have hyQc : y ∈ (Qᶜ : Set V) := Set.mem_compl hyQ
    have hxy' : (G.induce (Qᶜ : Set V)).Adj ⟨x, hxQc⟩ ⟨y, hyQc⟩ := hxy
    simp only [hxQ, hyQ, ↓reduceDIte]
    exact C.valid hxy'

/-- `G* = (G.induce Qᶜ) ⊔ edge ystar zstar` is `Δ`-colourable by the inductive hypothesis. -/
theorem colorable_surgery_graph
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hH : ¬ cliqueMinusEdge (Δ - 1) ⊑ G)
    (hreg' : G.IsRegularOfDegree Δ)
    {Q : Set V} [DecidablePred (· ∈ Q)]
    {k : ℕ} (hcardQc : Fintype.card ↥(Qᶜ : Set V) ≤ k)
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree)
    {ystar zstar : V}
    (hystar_Qc : ystar ∈ (Qᶜ : Set V)) (hzstar_Qc : zstar ∈ (Qᶜ : Set V))
    (_hne : ystar ≠ zstar)
    {y z : V} (hyQ : y ∈ Q) (hzQ : z ∈ Q)
    (hyAdj : G.Adj y ystar) (hzAdj : G.Adj z zstar) :
    (G.induce (Qᶜ : Set V) ⊔
      edge (⟨ystar, hystar_Qc⟩ : ↥(Qᶜ : Set V)) ⟨zstar, hzstar_Qc⟩).Colorable Δ := by
  classical
  set yS : ↥(Qᶜ : Set V) := ⟨ystar, hystar_Qc⟩
  set zS : ↥(Qᶜ : Set V) := ⟨zstar, hzstar_Qc⟩
  set Gstar := G.induce (Qᶜ : Set V) ⊔ edge yS zS
  have hΔstar : Gstar.maxDegree ≤ Δ := by
    refine maxDegree_le_of_forall_degree_le _ _ fun v => ?_
    have hdeg_le : (G.induce (Qᶜ : Set V)).degree v ≤ Δ := by
      have hsub :
          ((G.induce (Qᶜ : Set V)).neighborFinset v).map
            (Function.Embedding.subtype (· ∈ (Qᶜ : Set V))) ⊆ G.neighborFinset ↑v := by
        intro x hx
        rcases Finset.mem_map.1 hx with ⟨a, ha, rfl⟩
        exact (mem_neighborFinset _ _ _).2 ((mem_neighborFinset (G.induce (Qᶜ : Set V)) _ _).1 ha)
      have hle := Finset.card_le_card hsub
      rw [Finset.card_map, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hle
      exact hle.trans_eq (hreg' _)
    by_cases hv : (v : V) = ystar ∨ (v : V) = zstar
    · have hdrop : (G.induce (Qᶜ : Set V)).degree v ≤ Δ - 1 := by
        have hmem : ∃ x ∈ Q, G.Adj ↑v x := by
          rcases hv with h | h
          · exact ⟨y, hyQ, by simpa [h] using hyAdj.symm⟩
          · exact ⟨z, hzQ, by simpa [h] using hzAdj.symm⟩
        obtain ⟨x, hxQ, hxAdj⟩ := hmem
        have hxN : x ∈ G.neighborFinset ↑v := (mem_neighborFinset _ _ _).2 hxAdj
        have hsub :
            ((G.induce (Qᶜ : Set V)).neighborFinset v).map
              (Function.Embedding.subtype (· ∈ (Qᶜ : Set V))) ⊆
                (G.neighborFinset ↑v).erase x := by
          intro a ha
          rcases Finset.mem_map.1 ha with ⟨b, hb, rfl⟩
          have hb' : G.Adj ↑v ↑b := (mem_neighborFinset (G.induce (Qᶜ : Set V)) _ _).1 hb
          have hne_xb : (b : V) ≠ x := fun heq =>
            (Set.notMem_compl_iff.mpr hxQ) (heq ▸ b.property)
          exact Finset.mem_erase.2 ⟨hne_xb, (mem_neighborFinset _ _ _).2 hb'⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_map, card_neighborFinset_eq_degree,
          Finset.card_erase_of_mem hxN, card_neighborFinset_eq_degree, hreg'] at hle
        exact hle
      exact (degree_sup_edge_le (G := G.induce (Qᶜ : Set V)) yS zS v).trans (by omega)
    · have hEq : Gstar.degree v = (G.induce (Qᶜ : Set V)).degree v := by
        rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
        congr 1
        ext w
        simp only [mem_neighborFinset, Gstar, sup_adj, edge_adj]
        constructor
        · intro h
          exact h.resolve_right (by
            intro hpair
            rcases hpair.1 with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact hv (Or.inl (Subtype.ext_iff.mp h1))
            · exact hv (Or.inr (Subtype.ext_iff.mp h1)))
        · exact Or.inl
      exact hEq ▸ hdeg_le
  have hcfstar : Gstar.CliqueFree (Δ + 1) := by
    have hH' : ¬ cliqueMinusEdge (Δ - 1) ⊑ G.induce (Qᶜ : Set V) := fun h =>
      hH (h.trans (Copy.induce G (Qᶜ : Set V)).isContained)
    have := cliqueFree_sup_edge_of_cliqueMinusEdge_free (G := G.induce (Qᶜ : Set V))
      (k := Δ - 1) yS zS hH'
    convert this using 1; omega
  exact colorable_of_card_le_of_maxDegree_le (fun G => ih G) Gstar hcardQc hΔ3 hΔstar hcfstar

/-- An induced clique of size `n` is `(n-1)`-regular. -/
theorem isRegularOfDegree_induce_of_isClique [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {Q : Set V} [DecidablePred (· ∈ Q)] {n : ℕ}
    (hQclique : G.IsClique Q) (hQcard : Fintype.card ↥Q = n) :
    (G.induce Q).IsRegularOfDegree (n - 1) := by
  intro v
  rw [← ncard_neighborSet, G.induce_eq_top.mpr hQclique, ncard_neighborSet]
  simpa only [hQcard] using (IsRegularOfDegree.top (V := ↥Q) v)

/-- An induced clique on a nonempty set is connected. -/
theorem connected_induce_of_isClique [DecidableEq V]
    {Q : Set V} [Nonempty ↥Q] (hQclique : G.IsClique Q) :
    (G.induce Q).Connected := by
  rw [G.induce_eq_top.mpr hQclique]
  exact connected_top


end SimpleGraph

end
