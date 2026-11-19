import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric

/-! The parity splits of a twenty-two-vertex half after suppressing its cut endpoints. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree)
open private paritySide parity_bipartite parity_union parts_card sum_degrees_parts
  coordinate_slice_degree_cases coordinate_slice_low_independent low_slice_card_eq_q
  balanced_subset from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private SideHigh compressed compressed_degree compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private compressed_edge_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric
open private side_high_neighbors_card high_neighbors_compressed_separated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta
open private two_neighbor_table from
  D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
open private SimpleGraph.cycle_iso_of_connected_degree_le_two from
  D5.S3.Combinatorics.Graph.Brooks.General

private def pairingModel (opposite : Bool) : Fin 6 → Fin 6 :=
  if opposite then ![3, 4, 5, 0, 1, 2] else ![2, 4, 0, 5, 1, 3]

private def cycleLabel (shift : Fin 6) (reverse : Bool) (i : Fin 6) : Fin 6 :=
  if reverse then shift - i else shift + i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check the six possible first values separately in the kernel.
private theorem checked_pairing_values (a : Fin 6) :
    ∀ b c d e f : Fin 6,
      let m : Fin 6 → Fin 6 := ![a, b, c, d, e, f]
      (∀ i, m (m i) = i ∧ m i ≠ i ∧ ¬(cycleGraph 6).Adj i (m i)) →
      ∃ (shift : Fin 6) (reverse opposite : Bool), ∀ i,
        m (cycleLabel shift reverse i) = cycleLabel shift reverse (pairingModel opposite i) := by
  fin_cases a <;> decide +kernel

/-- A perfect matching of the six-cycle's vertices by nonedges has two possible
forms up to a rotation or reflection. -/
theorem cycle_pairing_normal_form (m : Fin 6 → Fin 6)
    (hm : ∀ i, m (m i) = i ∧ m i ≠ i ∧ ¬(cycleGraph 6).Adj i (m i)) :
    ∃ (shift : Fin 6) (reverse opposite : Bool), ∀ i,
      m (cycleLabel shift reverse i) = cycleLabel shift reverse (pairingModel opposite i) := by
  have he : (![m 0, m 1, m 2, m 3, m 4, m 5] : Fin 6 → Fin 6) = m := by
    funext i
    fin_cases i <;> rfl
  have h := checked_pairing_values (m 0) (m 1) (m 2) (m 3) (m 4) (m 5)
  dsimp only at h
  rw [he] at h
  exact h hm

#print axioms cycle_pairing_normal_form

attribute [local instance] Classical.propDecidable

private theorem three_vertices_not_three_edges {V : Type*} [Fintype V]
    (H : SimpleGraph V) (hV : Fintype.card V = 3)
    (htriangle : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) :
    H.edgeFinset.card ≠ 3 := by
  intro hE
  have hsum := H.sum_degrees_eq_twice_card_edges
  rw [hE] at hsum
  have hcap (x : V) : H.degree x ≤ 2 := by
    have h := H.degree_lt_card_verts x
    omega
  have hreg (x : V) : H.degree x = 2 := by
    by_contra hx
    have hlt : H.degree x < 2 := by have h := hcap x; omega
    have h := Finset.sum_lt_sum (s := (univ : Finset V))
      (fun y _ => hcap y) ⟨x, mem_univ _, hlt⟩
    simp only [Finset.sum_const, Finset.card_univ, hV, smul_eq_mul] at h
    omega
  have hall (x y : V) (hxy : x ≠ y) : H.Adj x y := by
    apply (H.degree_eq_card_sub_one x).mp
    · rw [hV, hreg]
    · exact hxy
  let e := (Fintype.equivFinOfCardEq hV).symm
  exact htriangle (e 0) (e 1) (e 2)
    (hall _ _ (e.injective.ne (by decide))) (hall _ _ (e.injective.ne (by decide)))
    (hall _ _ (e.injective.ne (by decide)))

private theorem five_vertices_six_edges {V : Type*} [Fintype V]
    (H : SimpleGraph V) (hV : Fintype.card V = 5)
    (hE : H.edgeFinset.card = 6)
    (htriangle : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) :
    Nonempty (H ≃g turanGraph 5 2) := by
  have hfree : H.CliqueFree 3 := by
    rw [cliqueFree_iff_isEmpty_copy_top_fin]
    constructor
    intro f
    exact htriangle (f 0) (f 1) (f 2)
      (f.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1))
      (f.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 1 2))
      (f.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 2 0))
  have hm : H.IsTuranMaximal 2 := by
    refine ⟨hfree, ?_⟩
    intro K _ hk
    have hle := hk.card_edgeFinset_le
    simpa [hV, hE, turanNumber_two] using hle
  exact hV ▸ hm.nonempty_iso_turanGraph

private theorem singleton_class_remainder
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : Fintype.card (SideHigh G L) = 1)
    (hR : Fintype.card (SideHigh G R) = 9) :
    ∃ r : SideHigh G L,
      let H := compressed G R
      let A := univ.filter (fun x : SideHigh G R => G.Adj r.val x.val)
      let B := univ \ A
      A.card = 3 ∧ B.card = 6 ∧
      (∀ x ∈ A, H.degree x = 2 ∧ H.neighborFinset x ⊆ B) ∧
      (∀ y ∈ B, ∃! x, x ∈ A ∧ H.Adj y x) ∧
      (H.induce (B : Set _)).IsRegularOfDegree 2 := by
  let H := compressed G R
  have hn : Nonempty (SideHigh G L) := Fintype.card_pos_iff.mp (by omega)
  let r : SideHigh G L := Classical.choice hn
  let A := univ.filter (fun x : SideHigh G R => G.Adj r.val x.val)
  let B := (univ : Finset (SideHigh G R)) \ A
  have hrL := (mem_filter.mp r.property).1
  have hr3 := (mem_filter.mp r.property).2
  have hr0 : (compressed G L).degree r = 0 := by
    have h := (compressed G L).degree_lt_card_verts r
    omega
  have hc := compressed_degree hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg r
  rw [hr0] at hc
  have ha := (side_high_neighbors_card hp hrL).trans (by omega :
    (degreeThree G (G.neighborFinset r.val)).card = 3)
  change A.card = 3 at ha
  have hb : B.card = 6 := by
    rw [show B.card = _ from card_sdiff_of_subset (subset_univ A), card_univ, hR, ha]
  have ha_mem (x : SideHigh G R) : x ∈ A ↔ G.Adj r.val x.val := by simp [A]
  have hb_mem (x : SideHigh G R) : x ∈ B ↔ x ∉ A := by simp [B]
  have hsep {x y : SideHigh G R} (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) :=
    high_neighbors_compressed_separated hp hg hrL hr3
      ((ha_mem x).mp hx) ((ha_mem y).mp hy) hne
  have hsub : Subsingleton (SideHigh G L) := by
    rw [← Fintype.card_le_one_iff_subsingleton]
    omega
  have hd (x : SideHigh G R) : H.degree x = if x ∈ A then 2 else 3 := by
    let M := univ.filter (fun y : SideHigh G L => G.Adj x.val y.val)
    have hm : M = if x ∈ A then {r} else ∅ := by
      ext y
      have hy : y = r := hsub.elim _ _
      subst y
      by_cases hx : x ∈ A
      · simp [M, hx, ((ha_mem x).mp hx).symm]
      · have h : ¬G.Adj x.val r.val := fun h => hx ((ha_mem x).mpr h.symm)
        simp [M, hx, h]
    have hN := side_high_neighbors_card hp.symm (mem_filter.mp x.property).1
    change M.card = _ at hN
    have hd := compressed_degree hp.symm hdeg (fun hxy hx hy => hlow hxy hx hy) hg x
    change H.degree x + _ = _ at hd
    rw [← hN, hm] at hd
    split_ifs at hd ⊢ <;> simp only [card_singleton, card_empty] at hd <;> omega
  have hneighbors (x : SideHigh G R) (hx : x ∈ A) : H.neighborFinset x ⊆ B := by
    intro y hy
    have hxy := (H.mem_neighborFinset _ _).mp hy
    exact (hb_mem y).mpr (fun hyA => (hsep hx hyA hxy.ne).1 hxy)
  have hdis : (A : Set (SideHigh G R)).PairwiseDisjoint (fun x => H.neighborFinset x) := by
    intro x hx y hy hxy
    exact disjoint_left.mpr fun z hxz hyz =>
      (hsep hx hy hxy).2 z ((H.mem_neighborFinset _ _).mp hxz) ((H.mem_neighborFinset _ _).mp hyz)
  have hcover : A.biUnion (fun x => H.neighborFinset x) = B := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := mem_biUnion.mp hy
      exact hneighbors x hx hxy
    · rw [card_biUnion hdis, hb]
      have hs : ∑ x ∈ A, (H.neighborFinset x).card = ∑ _x ∈ A, 2 := by
        apply sum_congr rfl
        intro x hx
        rw [H.card_neighborFinset_eq_degree, hd, ite_eq_left hx]
      rw [hs, sum_const, ha]
      decide
  have hmatch (y : SideHigh G R) (hy : y ∈ B) : ∃! x, x ∈ A ∧ H.Adj y x := by
    rw [← hcover] at hy
    obtain ⟨x, hx, hxy⟩ := mem_biUnion.mp hy
    have hxy := (H.mem_neighborFinset _ _).mp hxy
    refine ⟨x, ⟨hx, hxy.symm⟩, ?_⟩
    intro z hz
    by_contra hne
    exact (hsep hz.1 hx hne).2 y hz.2.symm hxy
  refine ⟨r, ha, hb, fun x hx => ⟨(hd x).trans (ite_eq_left hx), hneighbors x hx⟩, hmatch, ?_⟩
  intro y
  obtain ⟨x, hx, huniq⟩ := hmatch y.val y.property
  have hinter : H.neighborFinset y.val ∩ B = (H.neighborFinset y.val).erase x := by
    ext z
    rw [mem_inter, mem_erase, H.mem_neighborFinset, hb_mem]
    constructor
    · rintro ⟨hyz, hz⟩
      exact ⟨fun e => hz (e.symm ▸ hx.1), hyz⟩
    · rintro ⟨hne, hyz⟩
      exact ⟨hyz, fun hz => hne (huniq z ⟨hz, hyz⟩)⟩
  have hdY : H.degree y.val = 3 := by rw [hd, ite_eq_right ((hb_mem _).mp y.property)]
  have hc := congrArg Finset.card (H.map_neighborFinset_induce (s := (B : Set _)) y)
  rw [card_map, (H.induce (B : Set _)).card_neighborFinset_eq_degree,
    Finset.toFinset_coe, hinter, card_erase_of_mem ((H.mem_neighborFinset _ _).mpr hx.2),
    H.card_neighborFinset_eq_degree, hdY] at hc
  change (H.induce (B : Set _)).degree y = 2
  rw [← SimpleGraph.ncard_neighborSet] at hc ⊢
  exact hc.trans (show (3 : ℕ) - 1 = 2 by decide)

private theorem six_vertex_cycle {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hV : Fintype.card V = 6) (hreg : H.IsRegularOfDegree 2)
    (htriangle : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) :
    Nonempty (cycleGraph 6 ≃g H) := by
  have hcycles : H.IsCycles := by
    intro v _
    rw [H.ncard_neighborSet, hreg v]
  have hneighbor (v : V) : (H.neighborSet v).Nonempty :=
    H.degree_pos_iff_nonempty.mp (by rw [hreg v]; decide)
  have hn : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let a := Classical.choice hn
  obtain ⟨p, hp, hpc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.connectedComponentMk a) (v := a) rfl (hneighbor a)
  have hcomponent (v : V) : H.Reachable a v ↔ v ∈ p.support := by
    rw [← p.mem_verts_toSubgraph, hpc, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact reachable_comm
  have hlength {v : V} {w : H.Walk v v} (hw : w.IsCycle) : 4 ≤ w.length := by
    by_contra! h
    have h3 := hw.isCircuit.three_le_length
    obtain ⟨s, hs⟩ := (is3Clique_iff_exists_cycle_length_three (G := H)).mpr ⟨v, w, hw, by omega⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := is3Clique_iff.mp hs
    exact htriangle x y z hxy hyz hxz.symm
  have hcover (v : V) : v ∈ p.support := by
    by_contra hv
    obtain ⟨q, hq, _⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := H.connectedComponentMk v) (v := v) rfl (hneighbor v)
    have hdis : Disjoint p.support.toFinset q.support.toFinset := by
      apply Finset.disjoint_left.mpr
      intro w hwp hwq
      obtain ⟨r, _, _⟩ := q.mem_support_iff_exists_append.mp (List.mem_toFinset.mp hwq)
      exact hv ((hcomponent v).mp
        (((hcomponent w).mpr (List.mem_toFinset.mp hwp)).trans r.reachable.symm))
    have hc := card_le_card (subset_univ (p.support.toFinset ∪ q.support.toFinset))
    rw [card_union_of_disjoint hdis, hp.support_toFinset_card, hq.support_toFinset_card,
      card_univ, hV] at hc
    have hp4 := hlength hp
    have hq4 := hlength hq
    omega
  have hc : H.Connected := ⟨fun u v =>
    ((hcomponent u).mpr (hcover u)).symm.trans ((hcomponent v).mpr (hcover v))⟩
  have hiso := SimpleGraph.cycle_iso_of_connected_degree_le_two H hc
    (H.maxDegree_le_of_forall_degree_le 2 (fun v => (hreg v).le)) p hp
  have hu : p.support.toFinset = (univ : Finset V) := by ext v; simp [hcover v]
  have hl : p.length = 6 := by rw [← hp.support_toFinset_card, hu, card_univ, hV]
  exact hl ▸ hiso

private theorem normalize_cycle_attachments {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {A B : Finset V}
    (e : cycleGraph 6 ≃g H.induce (B : Set V))
    (hdegree : ∀ x ∈ A, H.degree x = 2 ∧ H.neighborFinset x ⊆ B)
    (hunique : ∀ y ∈ B, ∃! x, x ∈ A ∧ H.Adj y x)
    (htriangle : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) :
    ∃ (shift : Fin 6) (reverse opposite : Bool), ∀ i,
      ∃ x ∈ A, H.neighborFinset x =
        {(e (cycleLabel shift reverse i)).val,
          (e (cycleLabel shift reverse (pairingModel opposite i))).val} := by
  have he {i j : Fin 6} (h : (e i).val = (e j).val) : i = j :=
    e.injective (Subtype.ext h)
  have hpair (i : Fin 6) : ∃ j : Fin 6, j ≠ i ∧
      ∃ x ∈ A, H.neighborFinset x = {(e i).val, (e j).val} := by
    obtain ⟨x, ⟨hx, hix⟩, _⟩ := hunique (e i).val (e i).property
    obtain ⟨y, hyi, hyx, hN⟩ := two_neighbor_table (hdegree x hx).1 hix
    have hyB := (hdegree x hx).2 ((H.mem_neighborFinset x y).mpr hyx.symm)
    let j := e.symm ⟨y, hyB⟩
    have hj : (e j).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hyB⟩)
    refine ⟨j, fun h => hyi (hj.symm.trans (congrArg (fun z => (e z).val) h)), x, hx, ?_⟩
    rwa [hj]
  choose m hm using hpair
  have hends {x : V} {i j : Fin 6}
      (h : H.neighborFinset x = {(e i).val, (e j).val}) :
      H.Adj (e i).val x ∧ H.Adj (e j).val x := by
    constructor
    · have hi : (e i).val ∈ H.neighborFinset x := by
        rw [h]
        exact mem_insert_self _ _
      exact ((H.mem_neighborFinset _ _).mp hi).symm
    · have hj : (e j).val ∈ H.neighborFinset x := by
        rw [h]
        exact mem_insert_of_mem (mem_singleton_self _)
      exact ((H.mem_neighborFinset _ _).mp hj).symm
  have hvalid (i : Fin 6) :
      m (m i) = i ∧ m i ≠ i ∧ ¬(cycleGraph 6).Adj i (m i) := by
    obtain ⟨hi, x, hx, hN⟩ := hm i
    obtain ⟨hj, y, hy, hM⟩ := hm (m i)
    have hxy := (hunique (e (m i)).val (e (m i)).property).unique
      ⟨hx, (hends hN).2⟩ ⟨hy, (hends hM).1⟩
    subst y
    have hmem := (H.mem_neighborFinset x _).mpr (hends hM).2.symm
    rw [hN, mem_insert, mem_singleton] at hmem
    refine ⟨hmem.elim he (fun h => (hj (he h)).elim), hi, ?_⟩
    intro ha
    have ha' : H.Adj (e i).val (e (m i)).val := e.map_rel_iff.mpr ha
    exact htriangle _ _ _ ha' (hends hN).2 (hends hN).1.symm
  obtain ⟨shift, reverse, opposite, h⟩ := cycle_pairing_normal_form m hvalid
  refine ⟨shift, reverse, opposite, fun i => ?_⟩
  obtain ⟨_, x, hx, hN⟩ := hm (cycleLabel shift reverse i)
  rw [h i] at hN
  exact ⟨x, hx, hN⟩

private theorem singleton_class_cycle
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : Fintype.card (SideHigh G L) = 1)
    (hR : Fintype.card (SideHigh G R) = 9) :
    ∃ r : SideHigh G L,
      let H := compressed G R
      let A := univ.filter (fun x : SideHigh G R => G.Adj r.val x.val)
      let B := univ \ A
      A.card = 3 ∧
      (∀ x ∈ A, H.degree x = 2 ∧ H.neighborFinset x ⊆ B) ∧
      (∀ y ∈ B, ∃! x, x ∈ A ∧ H.Adj y x) ∧
      ∃ (e : cycleGraph 6 ≃g H.induce (B : Set _))
        (shift : Fin 6) (reverse opposite : Bool), ∀ i,
          ∃ x ∈ A, H.neighborFinset x =
            {(e (cycleLabel shift reverse i)).val,
              (e (cycleLabel shift reverse (pairingModel opposite i))).val} := by
  obtain ⟨r, ha, hb, hneighbors, hmatch, hreg⟩ :=
    singleton_class_remainder hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg hL hR
  have he := six_vertex_cycle _ (hreg := hreg) (hV := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_eq_fintype_card.trans (Fintype.card_coe _)).trans hb)
    (fun x y z => compressed_triangle_free hp.symm hg x.val y.val z.val)
  obtain ⟨e⟩ := he
  exact ⟨r, ha, hneighbors, hmatch, e,
    normalize_cycle_attachments e hneighbors hmatch (compressed_triangle_free hp.symm hg)⟩

/-- A 22-vertex coordinate half compresses to parity classes of orders 1 and 9,
with three disjoint pairs attached to a six-cycle, or to
two copies of the complete bipartite graph on parts of orders 2 and 3. -/
theorem half_compression {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 22) :
    ∃ p : Bool,
      let S := coordinateSlice C b
      let G := (hypercube 9).induce (S : Set (Q 9))
      let L := paritySide S p
      let R := paritySide S (!p)
      (Fintype.card (SideHigh G L) = 1 ∧ ∃ r : SideHigh G L,
        let H := compressed G R
        let A := univ.filter (fun x : SideHigh G R => G.Adj r.val x.val)
        let B := univ \ A
        A.card = 3 ∧
        (∀ x ∈ A, H.degree x = 2 ∧ H.neighborFinset x ⊆ B) ∧
        (∀ y ∈ B, ∃! x, x ∈ A ∧ H.Adj y x) ∧
        (∃ (e : cycleGraph 6 ≃g H.induce (B : Set _))
          (shift : Fin 6) (reverse opposite : Bool), ∀ i,
            ∃ x ∈ A, H.neighborFinset x =
              {(e (cycleLabel shift reverse i)).val,
                (e (cycleLabel shift reverse (pairingModel opposite i))).val})) ∨
      (Nonempty (compressed G L ≃g turanGraph 5 2) ∧
        Nonempty (compressed G R ≃g turanGraph 5 2)) := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  have hdeg (v : (S : Set (Q 9))) : G.degree v = 2 ∨ G.degree v = 3 :=
    coordinate_slice_degree_cases v.property hr
  have hlow {v w : (S : Set (Q 9))} (hvw : G.Adj v w)
      (hv : G.degree v = 2) (hw : G.degree w = 2) : False :=
    coordinate_slice_low_independent hr hb hvw hv hw
  have hcut : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hcount : (degreeTwo G univ).card = 12 := by
    rw [low_slice_card_eq_q hr]
    omega
  have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := parity_bipartite S
  have hd : Disjoint L R := by simpa only [Finset.disjoint_coe] using hp.disjoint
  have hu : L ∪ R = univ := parity_union S
  have hab : L.card + R.card = 22 := by
    rw [← card_union_of_disjoint hd, hu, card_univ]
    simpa using hs
  have hd₂ : Disjoint (degreeTwo G L) (degreeTwo G R) :=
    hd.mono (filter_subset _ _) (filter_subset _ _)
  have hu₂ : degreeTwo G L ∪ degreeTwo G R = degreeTwo G univ := by
    simp only [degreeTwo, ← filter_union, hu]
  have hlows : (degreeTwo G L).card + (degreeTwo G R).card = 12 := by
    rw [← card_union_of_disjoint hd₂, hu₂, hcount]
  have hsum : 2 * (degreeTwo G L).card + 3 * (degreeThree G L).card =
      2 * (degreeTwo G R).card + 3 * (degreeThree G R).card :=
    (sum_degrees_parts G hdeg L).symm.trans
      ((SimpleGraph.isBipartiteWith_sum_degrees_eq hp).trans (sum_degrees_parts G hdeg R))
  have hL := parts_card G hdeg L
  have hR := parts_card G hdeg R
  have hg := BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (filter_subset _ _))
  have heL := compressed_edge_count hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg
  have heR := compressed_edge_count hp.symm hdeg (fun hxy hx hy => hlow hxy hx hy) hg
  have hcard (T : Finset (S : Set (Q 9))) :
      Fintype.card (SideHigh G T) = (degreeThree G T).card := Fintype.card_coe _
  have hnL : (degreeThree G L).card ≠ 3 := by
    intro h
    have ht := compressed_triangle_free hp hg
    exact three_vertices_not_three_edges _ ((hcard L).trans h) ht (by omega)
  have hnR : (degreeThree G R).card ≠ 3 := by
    intro h
    have ht := compressed_triangle_free hp.symm hg
    exact three_vertices_not_three_edges _ ((hcard R).trans h) ht (by omega)
  have hsplit : (degreeThree G L).card = 1 ∨ (degreeThree G L).card = 5 ∨
      (degreeThree G R).card = 1 := by omega
  rcases hsplit with h | h | h
  · have hcL := (hcard L).trans h
    exact ⟨false, Or.inl ⟨hcL, singleton_class_cycle hp hdeg
      (fun hxy hx hy => hlow hxy hx hy) hg hcL ((hcard R).trans (by omega))⟩⟩
  · exact ⟨false, Or.inr
      ⟨five_vertices_six_edges _ ((hcard L).trans h) (heL.trans (by omega))
          (compressed_triangle_free hp hg),
        five_vertices_six_edges _ ((hcard R).trans (by omega)) (heR.trans (by omega))
          (compressed_triangle_free hp.symm hg)⟩⟩
  · have hcR := (hcard R).trans h
    exact ⟨true, Or.inl ⟨hcR, singleton_class_cycle hp.symm hdeg
      (fun hxy hx hy => hlow hxy hx hy) hg hcR ((hcard L).trans (by omega))⟩⟩

#print axioms half_compression

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression
