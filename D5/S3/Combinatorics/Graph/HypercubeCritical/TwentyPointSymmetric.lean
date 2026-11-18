/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSymmetric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSymmetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Actual compressed edge counts and degree alternatives in the twenty-point symmetric branch.
 -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta
import D5.S3.Combinatorics.Graph.Brooks.General
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! The symmetric auxiliary graphs are built from actual independent low paths. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric

open scoped BigOperators
open SimpleGraph GirthSliceCounting
open private SideHigh compressed compressed_degree compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private neighbor_parts_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private SimpleGraph.cycle_iso_of_connected_degree_le_two from
  D5.S3.Combinatorics.Graph.Brooks.General
open private side_high_neighbors_card high_neighbors_compressed_separated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta

attribute [local instance] Classical.propDecidable

private theorem compressed_edge_count
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    (compressed G L).edgeFinset.card = (degreeTwo G R).card := by
  let Hi := degreeThree G L
  let Lo := degreeTwo G R
  have hcomp (x : SideHigh G L) :
      (compressed G L).degree x = (degreeTwo G (G.neighborFinset x.val)).card := by
    have hc := compressed_degree hpart hdeg hlow hg x
    have hn := neighbor_parts_card hdeg x.val
    rw [(Finset.mem_filter.mp x.property).2] at hn
    omega
  have hsum : (∑ x : SideHigh G L, (compressed G L).degree x) =
      ∑ x ∈ Hi, (Lo.bipartiteAbove G.Adj x).card := by
    apply Finset.sum_bij (fun x _ => x.val)
    · intro x _; exact x.property
    · intro x _ y _ he; exact Subtype.ext he
    · intro x hx; exact ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
    · intro x _
      rw [hcomp]
      congr 1
      ext m
      simp only [degreeTwo, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        Lo, Finset.mem_bipartiteAbove]
      constructor
      · rintro ⟨hxm, hm2⟩
        exact ⟨⟨hpart.mem_of_mem_adj (Finset.mem_filter.mp x.property).1 hxm, hm2⟩, hxm⟩
      · rintro ⟨⟨_, hm2⟩, hxm⟩; exact ⟨hxm, hm2⟩
  have hlowcard (m : V) (hm : m ∈ Lo) : (Hi.bipartiteBelow G.Adj m).card = 2 := by
    have hm0 := Finset.mem_filter.mp hm
    have he : Hi.bipartiteBelow G.Adj m = G.neighborFinset m := by
      ext x
      simp only [Hi, degreeThree, Finset.mem_bipartiteBelow, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨_, hxm⟩; exact hxm.symm
      · intro hmx
        have hxL := hpart.mem_of_mem_adj' hm0.1 hmx.symm
        have hx3 : G.degree x = 3 := by
          rcases hdeg x with hx2 | hx3
          · exact (hlow hmx hm0.2 hx2).elim
          · exact hx3
        exact ⟨⟨hxL, hx3⟩, hmx.symm⟩
    rw [he, SimpleGraph.card_neighborFinset_eq_degree, hm0.2]
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow] at hsum
  have he := (compressed G L).sum_degrees_eq_twice_card_edges
  rw [hsum, Finset.sum_const_nat hlowcard] at he
  dsimp [Lo] at he
  omega

private theorem five_vertex_degree_cases
    {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (hV : Fintype.card V = 5) (hE : H.edgeFinset.card = 5)
    (hbound : ∀ x, H.degree x ≤ 3) :
    (∀ x, H.degree x = 2) ∨ ∃ x, H.degree x = 3 := by
  by_cases hmax : ∀ x, H.degree x ≤ 2
  · left
    intro x
    by_contra hx
    have hxlt : H.degree x < 2 := by have hh := hmax x; omega
    have hs := Finset.sum_lt_sum (s := Finset.univ)
      (fun y _ => hmax y) ⟨x, Finset.mem_univ _, hxlt⟩
    have hh := H.sum_degrees_eq_twice_card_edges
    rw [hE] at hh
    simp only [Finset.sum_const, Finset.card_univ, hV, smul_eq_mul] at hs
    omega
  · right
    push Not at hmax
    obtain ⟨x, hx⟩ := hmax
    exact ⟨x, by have hh := hbound x; omega⟩

private theorem symmetric_compression_degree_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL3 : (degreeThree G L).card = 5) (hR2 : (degreeTwo G R).card = 5) :
    Fintype.card (SideHigh G L) = 5 ∧ (compressed G L).edgeFinset.card = 5 ∧
      ((∀ x, (compressed G L).degree x = 2) ∨ ∃ x, (compressed G L).degree x = 3) := by
  have hcard : Fintype.card (SideHigh G L) = 5 := by
    simpa only [SideHigh, Fintype.card_coe] using hL3
  have he : (compressed G L).edgeFinset.card = 5 :=
    (compressed_edge_count hpart hdeg hlow hg).trans hR2
  refine ⟨hcard, he, five_vertex_degree_cases hcard he ?_⟩
  intro x
  have hc := compressed_degree hpart hdeg hlow hg x
  omega

private theorem five_two_regular_cycle
    {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (hV : Fintype.card V = 5) (hdegree : ∀ x, H.degree x = 2) :
    Nonempty (cycleGraph 5 ≃g H) := by
  have hn : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let a : V := Classical.choice hn
  have hcycles : H.IsCycles := by
    intro v _
    rw [H.ncard_neighborSet, hdegree]
  have hneighbor (v : V) : (H.neighborSet v).Nonempty := by
    apply (H.degree_pos_iff_nonempty).mp
    rw [hdegree]
    norm_num
  obtain ⟨p, hp, hpc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.connectedComponentMk a) (v := a) rfl (hneighbor a)
  have hcomponent (v : V) : H.Reachable a v ↔ v ∈ p.support := by
    rw [← p.mem_verts_toSubgraph, hpc, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact reachable_comm
  have hcover (v : V) : v ∈ p.support := by
    by_contra hv
    obtain ⟨q, hq, hqc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := H.connectedComponentMk v) (v := v) rfl (hneighbor v)
    have hdis : Disjoint p.support.toFinset q.support.toFinset := by
      apply Finset.disjoint_left.mpr
      intro w hwp hwq
      have hwpr := (hcomponent w).mpr (List.mem_toFinset.mp hwp)
      have hwqr : H.Reachable v w := by
        obtain ⟨r, s, _⟩ := q.mem_support_iff_exists_append.mp (List.mem_toFinset.mp hwq)
        exact r.reachable
      exact hv ((hcomponent v).mp (hwpr.trans hwqr.symm))
    have hc := Finset.card_le_card
      (Finset.subset_univ (p.support.toFinset ∪ q.support.toFinset))
    rw [Finset.card_union_of_disjoint hdis,
      hp.support_toFinset_card, hq.support_toFinset_card, Finset.card_univ, hV] at hc
    have hp3 := hp.isCircuit.three_le_length
    have hq3 := hq.isCircuit.three_le_length
    omega
  have hconnected : H.Connected := by
    refine ⟨?_⟩
    intro x y
    exact ((hcomponent x).mpr (hcover x)).symm.trans ((hcomponent y).mpr (hcover y))
  have hiso := SimpleGraph.cycle_iso_of_connected_degree_le_two H hconnected
    (H.maxDegree_le_of_forall_degree_le 2 (fun v => by rw [hdegree])) p hp
  have hu : p.support.toFinset = (Finset.univ : Finset V) := by
    ext v; simp [hcover v]
  have hlen : p.length = 5 := by
    rw [← hp.support_toFinset_card, hu, Finset.card_univ, hV]
  change Nonempty (cycleGraph p.length ≃g H) at hiso
  rw [hlen] at hiso
  exact hiso

private theorem five_degree_three_square_leaf
    {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (hV : Fintype.card V = 5) (hE : H.edgeFinset.card = 5)
    (htri : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False)
    {r : V} (hr3 : H.degree r = 3) :
    ∃ s a b c, [r, s, a, b, c].Nodup ∧
      H.neighborFinset r = {a, b, c} ∧ H.neighborFinset s = {a, b} ∧
      H.neighborFinset a = {r, s} ∧ H.neighborFinset b = {r, s} ∧
      H.neighborFinset c = {r} := by
  let N := H.neighborFinset r
  have hN3 : N.card = 3 := hr3
  have hrN : r ∉ N := H.notMem_neighborFinset_self r
  have hT : (insert r N).card = 4 := by rw [Finset.card_insert_of_notMem hrN, hN3]
  have hrest : (Finset.univ \ insert r N).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hV, hT]
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hrest
  have hsrest : s ∈ Finset.univ \ insert r N := by rw [hs]; simp
  have hsnot := (Finset.mem_sdiff.mp hsrest).2
  have hsr : s ≠ r := fun he => hsnot (Finset.mem_insert.mpr (Or.inl he))
  have hsN : s ∉ N := fun h => hsnot (Finset.mem_insert_of_mem h)
  have hcover (x : V) : x ∈ ({r, s} : Finset V) ∨ x ∈ N := by
    by_cases hx : x ∈ insert r N
    · rcases Finset.mem_insert.mp hx with he | hx
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl he))
      · exact Or.inr hx
    · have hxrest : x ∈ Finset.univ \ insert r N := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
      rw [hs, Finset.mem_singleton] at hxrest
      exact Or.inl (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hxrest)))
  have hdis : Disjoint ({r, s} : Finset V) N := by
    apply Finset.disjoint_left.mpr
    intro x hx hxN
    rcases Finset.mem_insert.mp hx with he | he
    · exact hrN (he ▸ hxN)
    · exact hsN (Finset.mem_singleton.mp he ▸ hxN)
  have hNind {x y : V} (hx : x ∈ N) (hy : y ∈ N) : ¬ H.Adj x y := by
    intro hxy
    exact htri r x y ((H.mem_neighborFinset _ _).mp hx) hxy
      (((H.mem_neighborFinset _ _).mp hy).symm)
  have hpairind {x y : V} (hx : x ∈ ({r, s} : Finset V))
      (hy : y ∈ ({r, s} : Finset V)) : ¬ H.Adj x y := by
    intro hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact H.ne_of_adj hxy rfl
    · exact hsN ((H.mem_neighborFinset _ _).mpr hxy)
    · exact hsN ((H.mem_neighborFinset _ _).mpr hxy.symm)
    · exact H.ne_of_adj hxy rfl
  have hp : H.IsBipartiteWith (({r, s} : Finset V) : Set V) (N : Set V) := by
    refine ⟨by exact_mod_cast hdis, ?_⟩
    intro x y hxy
    rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
    · exact (hpairind hx hy hxy).elim
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
    · exact (hNind hx hy hxy).elim
  have hu : ({r, s} : Finset V) ∪ N = Finset.univ := by
    ext x; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hcover x
  have hbalance := SimpleGraph.isBipartiteWith_sum_degrees_eq (s := {r, s}) (t := N) hp
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hsum' : (∑ x ∈ ({r, s} : Finset V), H.degree x) + ∑ x ∈ N, H.degree x = 10 := by
    rw [← Finset.sum_union hdis, hu, hsum, hE]
  have hleft : (∑ x ∈ ({r, s} : Finset V), H.degree x) = 3 + H.degree s := by
    simp [hsr.symm, hr3]
  rw [hleft] at hbalance hsum'
  have hs2 : H.degree s = 2 := by omega
  obtain ⟨a, b, hab, hNs⟩ := Finset.card_eq_two.mp
    (show (H.neighborFinset s).card = 2 from hs2)
  have haN : a ∈ N := hp.mem_of_mem_adj (by simp : s ∈ ({r, s} : Finset V))
    ((H.mem_neighborFinset _ _).mp (by rw [hNs]; simp))
  have hbN : b ∈ N := hp.mem_of_mem_adj (by simp : s ∈ ({r, s} : Finset V))
    ((H.mem_neighborFinset _ _).mp (by rw [hNs]; simp))
  have hrestN : (N \ {a, b}).card = 1 := by
    rw [Finset.card_sdiff_of_subset (by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨haN, hbN⟩),
      hN3, Finset.card_pair hab]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hrestN
  have hcRest : c ∈ N \ {a, b} := by rw [hc]; simp
  have hcN := (Finset.mem_sdiff.mp hcRest).1
  have hca : c ≠ a := fun he => (Finset.mem_sdiff.mp hcRest).2 (by simp [he])
  have hcb : c ≠ b := fun he => (Finset.mem_sdiff.mp hcRest).2 (by simp [he])
  have hN : N = {a, b, c} := (Finset.eq_of_subset_of_card_le
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨haN, hbN, hcN⟩)
    (by simp [hN3, hab, hca.symm, hcb.symm])).symm
  have htable (x : V) (hx : x ∈ N) : H.neighborFinset x ⊆ {r, s} := by
    intro y hy
    exact hp.mem_of_mem_adj' hx (((H.mem_neighborFinset _ _).mp hy).symm)
  have htab (x : V) (hxN : x ∈ N) (hxs : H.Adj x s) : H.neighborFinset x = {r, s} := by
    apply Finset.Subset.antisymm (htable x hxN)
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, SimpleGraph.mem_neighborFinset]
    exact ⟨((H.mem_neighborFinset _ _).mp hxN).symm, hxs⟩
  have hNc : H.neighborFinset c = {r} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_insert.mp (htable c hcN hx) with hxr | hxs
      · exact Finset.mem_singleton.mpr hxr
      · have hcs : H.Adj s c := ((H.mem_neighborFinset _ _).mp hx).symm
          |> fun h => Finset.mem_singleton.mp hxs ▸ h
        have hcm := (H.mem_neighborFinset _ _).mpr hcs
        rw [hNs] at hcm
        exact ((Finset.mem_insert.mp hcm).elim hca (fun h => hcb (Finset.mem_singleton.mp h))).elim
    · intro hx
      have he := Finset.mem_singleton.mp hx
      subst x
      exact (H.mem_neighborFinset _ _).mpr (((H.mem_neighborFinset _ _).mp hcN).symm)
  have hout (x : V) (hx : x ∈ N) : r ≠ x ∧ s ≠ x :=
    ⟨fun he => hrN (he.symm ▸ hx), fun he => hsN (he.symm ▸ hx)⟩
  refine ⟨s, a, b, c, ?_, hN, hNs,
    htab a haN (((H.mem_neighborFinset _ _).mp (by rw [hNs]; simp)).symm),
    htab b hbN (((H.mem_neighborFinset _ _).mp (by rw [hNs]; simp)).symm), hNc⟩
  simp [List.nodup_cons, hsr.symm, (hout a haN).1, (hout b hbN).1,
    (hout c hcN).1, (hout a haN).2, (hout b hbN).2, (hout c hcN).2,
    hab, hca.symm, hcb.symm]

private def SquareLeaf {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) : Prop :=
  ∃ r s a b c, [r, s, a, b, c].Nodup ∧
    H.neighborFinset r = {a, b, c} ∧ H.neighborFinset s = {a, b} ∧
    H.neighborFinset a = {r, s} ∧ H.neighborFinset b = {r, s} ∧
    H.neighborFinset c = {r}

private theorem symmetric_compression_types
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL3 : (degreeThree G L).card = 5) (hR2 : (degreeTwo G R).card = 5)
    (htri : ∀ x y z, (compressed G L).Adj x y → (compressed G L).Adj y z →
      (compressed G L).Adj z x → False) :
    Nonempty (cycleGraph 5 ≃g compressed G L) ∨ SquareLeaf (compressed G L) := by
  obtain ⟨hV, hE, hcases⟩ := symmetric_compression_degree_cases hpart hdeg hlow hg hL3 hR2
  rcases hcases with htwo | ⟨r, hr⟩
  · exact Or.inl (five_two_regular_cycle hV htwo)
  · exact Or.inr ⟨r, five_degree_three_square_leaf hV hE htri hr⟩

private theorem cycle_five_close (i j : Fin 5) (hij : i ≠ j) :
    (cycleGraph 5).Adj i j ∨ ∃ k, (cycleGraph 5).Adj i k ∧ (cycleGraph 5).Adj j k := by
  revert i j
  decide

private theorem no_cycle_opposite_leaf
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hiso : Nonempty (cycleGraph 5 ≃g compressed G R))
    {c : SideHigh G L} (hc1 : (compressed G L).degree c = 1) : False := by
  have hcL := (Finset.mem_filter.mp c.property).1
  have hc3 := (Finset.mem_filter.mp c.property).2
  have hd := compressed_degree hpart hdeg hlow hg c
  rw [hc1] at hd
  have hh : (degreeThree G (G.neighborFinset c.val)).card = 2 := by omega
  have hc := side_high_neighbors_card hpart hcL
  rw [hh] at hc
  obtain ⟨x, y, hxy, hN⟩ := Finset.card_eq_two.mp hc
  have hx : G.Adj c.val x.val := (Finset.mem_filter.mp
    (show x ∈ (Finset.univ : Finset (SideHigh G R)).filter (fun t => G.Adj c.val t.val) by
      rw [hN]; simp)).2
  have hy : G.Adj c.val y.val := (Finset.mem_filter.mp
    (show y ∈ (Finset.univ : Finset (SideHigh G R)).filter (fun t => G.Adj c.val t.val) by
      rw [hN]; simp)).2
  have hsep := high_neighbors_compressed_separated hpart hg hcL hc3 hx hy hxy
  obtain ⟨e⟩ := hiso
  rcases cycle_five_close (e.symm x) (e.symm y)
      (fun he => hxy (e.symm.injective he)) with he | ⟨k, hxk, hyk⟩
  · apply hsep.1
    simpa only [e.apply_symm_apply] using e.map_rel_iff.mpr he
  · apply hsep.2 (e k)
    · simpa only [e.apply_symm_apply] using e.map_rel_iff.mpr hxk
    · simpa only [e.apply_symm_apply] using e.map_rel_iff.mpr hyk

private theorem symmetric_paired_types
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL3 : (degreeThree G L).card = 5) (hR3 : (degreeThree G R).card = 5)
    (hL2 : (degreeTwo G L).card = 5) (hR2 : (degreeTwo G R).card = 5) :
    (Nonempty (cycleGraph 5 ≃g compressed G L) ∧
      Nonempty (cycleGraph 5 ≃g compressed G R)) ∨
    (SquareLeaf (compressed G L) ∧ SquareLeaf (compressed G R)) := by
  have hL := symmetric_compression_types hpart hdeg hlow hg hL3 hR2
    (compressed_triangle_free hpart hg)
  have hR := symmetric_compression_types hpart.symm hdeg hlow hg hR3 hL2
    (compressed_triangle_free hpart.symm hg)
  rcases hL with hLc | hLs <;> rcases hR with hRc | hRs
  · exact Or.inl ⟨hLc, hRc⟩
  · obtain ⟨r, s, a, b, c, _, _, _, _, _, hc⟩ := hRs
    have hc1 : (compressed G R).degree c = 1 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hc, Finset.card_singleton]
    exact (no_cycle_opposite_leaf hpart.symm hdeg hlow hg hLc hc1).elim
  · obtain ⟨r, s, a, b, c, _, _, _, _, _, hc⟩ := hLs
    have hc1 : (compressed G L).degree c = 1 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hc, Finset.card_singleton]
    exact (no_cycle_opposite_leaf hpart hdeg hlow hg hRc hc1).elim
  · exact Or.inr ⟨hLs, hRs⟩

#print axioms symmetric_paired_types

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric
