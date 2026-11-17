/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceTree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Sharp double-root counts and the nineteen-vertex equality tree. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeFiveNeighborGap
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSlice

attribute [local simp] decide_eq_true_eq Finset.filter_insert Finset.filter_singleton

open scoped BigOperators Classical
open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open private neighbor_parts_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private diff from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_symm diff_empty_iff diff_triangle_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport
open private diff_double from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeFiveNeighborGap
open private Labels Labels.A Labels.B Labels.M Labels.high_inj Labels.neighbors
  Labels.row_inj Labels.col_inj Labels.cover Labels.mk normal_labels from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicalSubdivisionRigidity
open private coordinate_slice_degree_cases low_slice_card_eq_q
  coordinate_slice_low_independent balanced_subset paritySide parity_union parity_bipartite
  parts_card sum_degrees_parts twice_low_le_three_high from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private armData armMiddleData armLevelOne armLevelTwo armLevelThree
  armMiddleSecond armEndpoint armData_card_lower armMiddleData_card_lower
  arm_level_one_card arm_level_two_card arm_level_three_card arm_levels_disjoint
  arm_level_one_spec arm_level_two_spec arm_level_three_spec sideTree sideTree_card
  sideTree_path sideTrees_disjoint double_root_count first_low_of_middle_two
  high_edge_exists short_paths_unique_seven highWithHigh high_neighbor_deficit
  roots middles leaves global_layers_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice

private theorem arm_middle_high_count
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    {r c : V} (hr : G.degree r = 3) (hrc : G.Adj r c) :
    (armMiddleData G r c).card =
      2 + (degreeThree G (armLevelOne G r c)).card := by
  have he (a : V) (ha : a ∈ (G.neighborFinset r).erase c) :
      ((G.neighborFinset a).erase r).card = 1 + if G.degree a = 3 then 1 else 0 := by
    have har := ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ha).2).symm
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr har),
      SimpleGraph.card_neighborFinset_eq_degree]
    rcases hdeg a with h | h <;> simp [h]
  have hf := arm_level_one_card G r c hr hrc
  simp only [armMiddleData,Finset.card_sigma]
  rw [Finset.sum_congr rfl he,Finset.sum_add_distrib]
  simpa [degreeThree,armLevelOne,Finset.sum_boole] using
    congrArg (fun k => k + (degreeThree G (armLevelOne G r c)).card) hf

private theorem double_root_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c)
    (hr : G.degree r = 3) (hc : G.degree c = 3) :
    18 + (degreeThree G (armLevelOne G r c)).card +
      (degreeThree G (armLevelOne G c r)).card ≤ Fintype.card V := by
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  have hdis := sideTrees_disjoint hpart hg hrL hrc
  have ht1 := sideTree_card hpart hg hrL hrc hr
  have ht2 := sideTree_card hpart.symm hg hcR hrc.symm hc
  have hm1 := arm_middle_high_count G hdeg hr hrc
  have hm2 := arm_middle_high_count G hdeg hc hrc.symm
  have he1 := armData_card_lower G r c hr hdeg hlow hrc
  have he2 := armData_card_lower G c r hc hdeg hlow hrc.symm
  have hcard := Finset.card_le_card (Finset.subset_univ (sideTree G r c ∪ sideTree G c r))
  rw [Finset.card_union_of_disjoint hdis,Finset.card_univ] at hcard
  omega

private theorem eleven_low_nineteen_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {r c : V} (hrL : r ∈ L) (hrc : G.Adj r c)
    (hr : G.degree r = 3) (hc : G.degree c = 3)
    (hN : Fintype.card V = 19) (hq : (degreeTwo G Finset.univ).card = 11) : False := by
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  have hp := parts_card G hdeg Finset.univ
  rw [Finset.card_univ] at hp
  have hhigh : (degreeThree G Finset.univ).card = 8 := by omega
  have hbad : (highWithHigh G).card ≤ 2 := by
    have hh := high_neighbor_deficit G hdeg hlow
    omega
  have hrccard : (roots r c).card = 2 := by simp [roots,G.ne_of_adj hrc]
  have hrootsbad : roots r c ⊆ highWithHigh G := by
    intro x hx
    simp only [roots,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,c,hrc,hc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,r,hrc.symm,hr⟩
  have hbad_eq : highWithHigh G = roots r c :=
    (Finset.eq_of_subset_of_card_le hrootsbad (by omega)).symm
  have hfirst (a : V) (ha : a ∈ armLevelOne G r c) : G.degree a = 2 := by
    rcases hdeg a with h | h
    · exact h
    · have hab := (arm_level_one_spec ha).2
      have hb : a ∈ highWithHigh G := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,r,hab.symm,hr⟩
      rw [hbad_eq] at hb
      simp only [roots,Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with he | he
      · exact (G.ne_of_adj hab he.symm).elim
      · exact ((arm_level_one_spec ha).1 he).elim
  have hfirst' (a : V) (ha : a ∈ armLevelOne G c r) : G.degree a = 2 := by
    rcases hdeg a with h | h
    · exact h
    · have hab := (arm_level_one_spec ha).2
      have hb : a ∈ highWithHigh G := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,c,hab.symm,hc⟩
      rw [hbad_eq] at hb
      simp only [roots,Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with he | he
      · exact ((arm_level_one_spec ha).1 he).elim
      · exact (G.ne_of_adj hab he.symm).elim
  have hm1 : (armMiddleData G r c).card = 2 := by
    rw [arm_middle_high_count G hdeg hr hrc]
    have hz : degreeThree G (armLevelOne G r c) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have h2 := hfirst a (Finset.mem_filter.mp ha).1
      have h3 := (Finset.mem_filter.mp ha).2
      omega
    simp [hz]
  have hm2 : (armMiddleData G c r).card = 2 := by
    rw [arm_middle_high_count G hdeg hc hrc.symm]
    have hz : degreeThree G (armLevelOne G c r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have h2 := hfirst' a (Finset.mem_filter.mp ha).1
      have h3 := (Finset.mem_filter.mp ha).2
      omega
    simp [hz]
  let T := sideTree G r c ∪ sideTree G c r
  have hT : 18 ≤ T.card := by
    have hdis := sideTrees_disjoint hpart hg hrL hrc
    have ht1 := sideTree_card hpart hg hrL hrc hr
    have ht2 := sideTree_card hpart.symm hg hcR hrc.symm hc
    have he1 := armData_card_lower G r c hr hdeg hlow hrc
    have he2 := armData_card_lower G c r hc hdeg hlow hrc.symm
    change 18 ≤ (sideTree G r c ∪ sideTree G c r).card
    rw [Finset.card_union_of_disjoint hdis]
    omega
  have hout : (Finset.univ \ T).card ≤ 1 := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
    rw [Finset.card_univ] at hh
    omega
  have hmcard : (middles G r c).card ≤ 4 := by
    have hh := Finset.card_union_le (armLevelTwo G r c) (armLevelTwo G c r)
    rw [arm_level_two_card hpart hg hrL hrc,
      arm_level_two_card hpart.symm hg hcR hrc.symm] at hh
    change (armLevelTwo G r c ∪ armLevelTwo G c r).card ≤ 4
    omega
  obtain ⟨hrm,hrml⟩ := global_layers_disjoint hpart hg hrL hrc
  have hleaf : ∀ x ∈ leaves G r c, G.degree x ≠ 3 := by
    intro x hx hx3
    have hparent : ∃ s, s ∈ middles G r c ∧ G.degree s = 3 ∧ G.Adj x s := by
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨a,s,ha,hs,he⟩ := arm_level_three_spec hx
        have ha2 := hfirst a ha
        have has := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2
        have hs3 : G.degree s = 3 := by
          rcases hdeg s with hs2 | hs3
          · exact (hlow has ha2 hs2).elim
          · exact hs3
        refine ⟨s,Finset.mem_union_left _ ?_,hs3,
          ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp he).2).symm⟩
        exact Finset.mem_image.mpr ⟨⟨a,s⟩,Finset.mem_sigma.mpr ⟨ha,hs⟩,rfl⟩
      · obtain ⟨a,s,ha,hs,he⟩ := arm_level_three_spec hx
        have ha2 := hfirst' a ha
        have has := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2
        have hs3 : G.degree s = 3 := by
          rcases hdeg s with hs2 | hs3
          · exact (hlow has ha2 hs2).elim
          · exact hs3
        refine ⟨s,Finset.mem_union_right _ ?_,hs3,
          ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp he).2).symm⟩
        exact Finset.mem_image.mpr ⟨⟨a,s⟩,Finset.mem_sigma.mpr ⟨ha,hs⟩,rfl⟩
    obtain ⟨s,_,hs3,hxs⟩ := hparent
    have hb : x ∈ highWithHigh G := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx3⟩,s,hxs,hs3⟩
    rw [hbad_eq] at hb
    exact Finset.disjoint_left.mp hrml (Finset.mem_union_left _ hb) hx
  have hcover : degreeThree G Finset.univ ⊆ roots r c ∪ middles G r c ∪ (Finset.univ \ T) := by
    intro x hx
    have hx3 := (Finset.mem_filter.mp hx).2
    by_cases hxT : x ∈ T
    · simp only [T,sideTree,Finset.mem_union,Finset.mem_singleton] at hxT
      simp only [roots,middles,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      rcases hxT with (((h | h) | h) | h) | (((h | h) | h) | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · have hh := hfirst x h; omega
      · exact Or.inl (Or.inr (Or.inl h))
      · exact (hleaf x (Finset.mem_union_left _ h) hx3).elim
      · exact Or.inl (Or.inl (Or.inr h))
      · have hh := hfirst' x h; omega
      · exact Or.inl (Or.inr (Or.inr h))
      · exact (hleaf x (Finset.mem_union_right _ h) hx3).elim
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hxT⟩)
  have hh := Finset.card_le_card hcover
  have hu := Finset.card_union_le (roots r c ∪ middles G r c) (Finset.univ \ T)
  have hu' := Finset.card_union_le (roots r c) (middles G r c)
  omega


private theorem high_fork_exists
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hq : (degreeTwo G Finset.univ).card = 9)
    (hh : (degreeThree G Finset.univ).card = 10) :
    ∃ r c w, G.degree r = 3 ∧ G.degree c = 3 ∧ G.degree w = 3 ∧
      G.Adj r c ∧ G.Adj r w ∧ c ≠ w := by
  by_contra hn
  have hsmall (r : V) (hr : r ∈ degreeThree G Finset.univ) :
      (degreeThree G (G.neighborFinset r)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro c hc w hw
    by_contra hcw
    exact hn ⟨r,c,w,(Finset.mem_filter.mp hr).2,(Finset.mem_filter.mp hc).2,
      (Finset.mem_filter.mp hw).2,
      (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hc).1,
      (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hw).1,hcw⟩
  have hleft (r : V) (hr : r ∈ degreeThree G Finset.univ) :
      2 ≤ ((degreeTwo G Finset.univ).bipartiteAbove G.Adj r).card := by
    have hparts := neighbor_parts_card hdeg r
    have hsmall' := hsmall r hr
    have hr3 := (Finset.mem_filter.mp hr).2
    have he : (degreeTwo G Finset.univ).bipartiteAbove G.Adj r =
        degreeTwo G (G.neighborFinset r) := by
      ext v
      simp [degreeTwo,Finset.mem_bipartiteAbove,SimpleGraph.mem_neighborFinset,and_comm]
    rw [he]
    omega
  have hright (w : V) (hw : w ∈ degreeTwo G Finset.univ) :
      ((degreeThree G Finset.univ).bipartiteBelow G.Adj w).card ≤ 2 := by
    have hs : (degreeThree G Finset.univ).bipartiteBelow G.Adj w ⊆ G.neighborFinset w := by
      intro v hv
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hv).2.symm
    have he := Finset.card_le_card hs
    rwa [SimpleGraph.card_neighborFinset_eq_degree,(Finset.mem_filter.mp hw).2] at he
  have he := Finset.card_mul_le_card_mul (r := G.Adj)
    (s := degreeThree G Finset.univ) (t := degreeTwo G Finset.univ)
    (m := 2) (n := 2) hleft hright
  omega

private theorem fork_equality_tree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {r c w : V} (hrL : r ∈ L) (hrc : G.Adj r c) (hrw : G.Adj r w)
    (hcw : c ≠ w) (hr : G.degree r = 3) (hc : G.degree c = 3)
    (hw : G.degree w = 3) (hN : Fintype.card V = 19) :
    degreeThree G (armLevelOne G r c) = {w} ∧
    degreeThree G (armLevelOne G c r) = ∅ ∧
    (armMiddleData G r c).card = 3 ∧ (armMiddleData G c r).card = 2 ∧
    (armData G r c).card = 4 ∧ (armData G c r).card = 4 ∧
    sideTree G r c ∪ sideTree G c r = Finset.univ := by
  have hbound := double_root_sharp hpart hg hdeg hlow hrL hrc hr hc
  have hwm : w ∈ degreeThree G (armLevelOne G r c) :=
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
      ⟨hcw.symm,(G.mem_neighborFinset _ _).mpr hrw⟩,hw⟩
  have hpos := Finset.card_pos.mpr ⟨w,hwm⟩
  have h1 : (degreeThree G (armLevelOne G r c)).card = 1 := by omega
  have h0 : (degreeThree G (armLevelOne G c r)).card = 0 := by omega
  have hm1 := arm_middle_high_count G hdeg hr hrc
  have hm2 := arm_middle_high_count G hdeg hc hrc.symm
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  have hdis := sideTrees_disjoint hpart hg hrL hrc
  have ht1 := sideTree_card hpart hg hrL hrc hr
  have ht2 := sideTree_card hpart.symm hg hcR hrc.symm hc
  have he1 := armData_card_lower G r c hr hdeg hlow hrc
  have he2 := armData_card_lower G c r hc hdeg hlow hrc.symm
  have hcard := Finset.card_le_card (Finset.subset_univ (sideTree G r c ∪ sideTree G c r))
  rw [Finset.card_union_of_disjoint hdis,Finset.card_univ] at hcard
  refine ⟨Finset.eq_singleton_iff_unique_mem.mpr ⟨hwm,?_⟩,
    Finset.card_eq_zero.mp h0,by omega,by omega,by omega,by omega,?_⟩
  · intro a ha
    exact Finset.card_le_one.mp (by omega) a ha w hwm
  · apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ,Finset.card_union_of_disjoint hdis]
    omega


private theorem forward_single
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {r a : V} (hra : G.Adj r a) (ha : G.degree a = 2) :
    ∃ x, x ≠ r ∧ G.Adj a x ∧ (G.neighborFinset a).erase r = {x} := by
  have hc : ((G.neighborFinset a).erase r).card = 1 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hra.symm),
      SimpleGraph.card_neighborFinset_eq_degree,ha]
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hc
  have hm : x ∈ (G.neighborFinset a).erase r := by rw [hx]; simp
  exact ⟨x,(Finset.mem_erase.mp hm).1,
    (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hm).2,hx⟩

private theorem forward_pair
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {r a : V} (hra : G.Adj r a) (ha : G.degree a = 3) :
    ∃ x y, x ≠ y ∧ x ≠ r ∧ y ≠ r ∧ G.Adj a x ∧ G.Adj a y ∧
      (G.neighborFinset a).erase r = {x,y} := by
  have hc : ((G.neighborFinset a).erase r).card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hra.symm),
      SimpleGraph.card_neighborFinset_eq_degree,ha]
  obtain ⟨x,y,hxy,hset⟩ := Finset.card_eq_two.mp hc
  have hxm : x ∈ (G.neighborFinset a).erase r := by rw [hset]; simp
  have hym : y ∈ (G.neighborFinset a).erase r := by rw [hset]; simp
  exact ⟨x,y,hxy,(Finset.mem_erase.mp hxm).1,(Finset.mem_erase.mp hym).1,
    (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hxm).2,
    (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hym).2,hset⟩

private theorem first_high_children_low
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {r c : V} (hr : G.degree r = 3) (hrc : G.Adj r c)
    (he : (armData G r c).card = 4)
    {a : V} (ha : a ∈ armLevelOne G r c) (ha3 : G.degree a = 3)
    {s : V} (hs : s ∈ (G.neighborFinset a).erase r) : G.degree s = 2 := by
  let W (a : V) := ∑ s ∈ (G.neighborFinset a).erase r,
    ((G.neighborFinset s).erase a).card
  have hper (a : V) (ha : a ∈ armLevelOne G r c) : 2 ≤ W a := by
    have hra := (arm_level_one_spec ha).2
    rcases hdeg a with ha2 | ha3
    · have hc : ((G.neighborFinset a).erase r).card = 1 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hra.symm),
          SimpleGraph.card_neighborFinset_eq_degree,ha2]
      have hb (s : V) (hs : s ∈ (G.neighborFinset a).erase r) :
          2 ≤ ((G.neighborFinset s).erase a).card := by
        have has := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2
        have hs3 : G.degree s = 3 := by
          rcases hdeg s with h2 | h3
          · exact (hlow has ha2 h2).elim
          · exact h3
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr has.symm),
          SimpleGraph.card_neighborFinset_eq_degree,hs3]
      have hh := Finset.sum_le_sum (s := (G.neighborFinset a).erase r) hb
      simpa [W,hc] using hh
    · have hc : ((G.neighborFinset a).erase r).card = 2 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hra.symm),
          SimpleGraph.card_neighborFinset_eq_degree,ha3]
      have hb (s : V) (hs : s ∈ (G.neighborFinset a).erase r) :
          1 ≤ ((G.neighborFinset s).erase a).card := by
        have has := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr has.symm),
          SimpleGraph.card_neighborFinset_eq_degree]
        rcases hdeg s with h | h <;> omega
      have hh := Finset.sum_le_sum (s := (G.neighborFinset a).erase r) hb
      simpa [W,hc] using hh
  rcases hdeg s with hs2 | hs3
  · exact hs2
  · have hc : ((G.neighborFinset a).erase r).card = 2 := by
      rw [Finset.card_erase_of_mem
        ((G.mem_neighborFinset _ _).mpr (arm_level_one_spec ha).2.symm),
        SimpleGraph.card_neighborFinset_eq_degree,ha3]
    have hb (t : V) (ht : t ∈ (G.neighborFinset a).erase r) :
        1 ≤ ((G.neighborFinset t).erase a).card := by
      have hat := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ht).2
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hat.symm),
        SimpleGraph.card_neighborFinset_eq_degree]
      rcases hdeg t with h | h <;> omega
    have hstrict : 1 < ((G.neighborFinset s).erase a).card := by
      have has := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hs).2
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr has.symm),
        SimpleGraph.card_neighborFinset_eq_degree,hs3]
      decide
    have hlt := Finset.sum_lt_sum hb ⟨s,hs,hstrict⟩
    have hWa : 2 < W a := by simpa [W,hc] using hlt
    have hsum := Finset.sum_lt_sum hper ⟨a,ha,hWa⟩
    have hfirst := arm_level_one_card G r c hr hrc
    have hsumeq : (∑ a ∈ armLevelOne G r c, W a) = (armData G r c).card := by
      simp [armData,armLevelOne,W,Finset.card_sigma]
    rw [hsumeq,he] at hsum
    simpa [hfirst] using hsum

private def treeParent : Fin 11 → Fin 19 := ![1,0,0,0,1,1,2,2,3,4,5]
private def treeChildren : Fin 11 → Finset (Fin 19) :=
  ![{2,3},{4,5},{6,7},{8},{9},{10},{11},{12},{13,14},{15,16},{17,18}]

private theorem fork_tree_vertices
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {r c w : V} (hrL : r ∈ L) (hrc : G.Adj r c) (hrw : G.Adj r w)
    (hcw : c ≠ w) (hr : G.degree r = 3) (hc : G.degree c = 3)
    (hw : G.degree w = 3) (hN : Fintype.card V = 19) :
    ∃ v : Fin 19 → V, Function.Injective v ∧ v 0 = r ∧ v 1 = c ∧ v 2 = w ∧
      (∀ i : Fin 11, (G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i))).erase (v (treeParent i)) =
        (treeChildren i).image v) ∧
      G.degree (v 11) = 3 ∧ G.degree (v 12) = 3 := by
  obtain ⟨hhi,hhi',hm1,hm2,he1,_,hcover⟩ :=
    fork_equality_tree hpart hg hdeg hlow hrL hrc hrw hcw hr hc hw hN
  have hcR := hpart.mem_of_mem_adj (show r ∈ (L : Set V) from hrL) hrc
  have hwm : w ∈ (G.neighborFinset r).erase c :=
    Finset.mem_erase.mpr ⟨hcw.symm,(G.mem_neighborFinset _ _).mpr hrw⟩
  have hfirst : ((G.neighborFinset r).erase c).card = 2 := arm_level_one_card G r c hr hrc
  have hzcard := Finset.card_erase_add_one hwm
  obtain ⟨z,hzset⟩ := Finset.card_eq_one.mp (show
      (((G.neighborFinset r).erase c).erase w).card = 1 by omega)
  have hzmem : z ∈ ((G.neighborFinset r).erase c).erase w := by rw [hzset]; simp
  have hzw : z ≠ w := (Finset.mem_erase.mp hzmem).1
  have hzm : z ∈ (G.neighborFinset r).erase c := (Finset.mem_erase.mp hzmem).2
  have hrz := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hzm).2
  have hrwz : (G.neighborFinset r).erase c = {w,z} := by
    rw [← Finset.insert_erase hwm,hzset]
  have hz2 : G.degree z = 2 := by
    rcases hdeg z with h2 | h3
    · exact h2
    · have hzhi : z ∈ degreeThree G (armLevelOne G r c) :=
        Finset.mem_filter.mpr ⟨hzm,h3⟩
      rw [hhi] at hzhi
      exact (hzw (Finset.mem_singleton.mp hzhi)).elim
  obtain ⟨A,B,hAB,hAr,hBr,hcA,hcB,hcAB⟩ := forward_pair hrc hc
  have hcfirst (a : V) (ha : a ∈ (G.neighborFinset c).erase r) : G.degree a = 2 := by
    rcases hdeg a with h2 | h3
    · exact h2
    · have hmem : a ∈ degreeThree G (armLevelOne G c r) := Finset.mem_filter.mpr ⟨ha,h3⟩
      rw [hhi'] at hmem
      exact (Finset.notMem_empty a hmem).elim
  have hA2 := hcfirst A (by rw [hcAB]; simp)
  have hB2 := hcfirst B (by rw [hcAB]; simp)
  obtain ⟨s,t,hst,hsr,htr,hws,hwt,hwst⟩ := forward_pair hrw hw
  have hs2 : G.degree s = 2 := first_high_children_low hdeg hlow hr hrc he1 hwm hw
    (by rw [hwst]; simp)
  have ht2 : G.degree t = 2 := first_high_children_low hdeg hlow hr hrc he1 hwm hw
    (by rw [hwst]; simp)
  obtain ⟨p,hpr,hzp,hzps⟩ := forward_single hrz hz2
  obtain ⟨a,hac,hAa,hAas⟩ := forward_single hcA hA2
  obtain ⟨b,hbc,hBb,hBbs⟩ := forward_single hcB hB2
  obtain ⟨x,hxw,hsx,hsxs⟩ := forward_single hws hs2
  obtain ⟨y,hyw,hty,htys⟩ := forward_single hwt ht2
  have hp3 : G.degree p = 3 := by
    rcases hdeg p with h2 | h3
    · exact (hlow hzp hz2 h2).elim
    · exact h3
  have ha3 : G.degree a = 3 := by
    rcases hdeg a with h2 | h3
    · exact (hlow hAa hA2 h2).elim
    · exact h3
  have hb3 : G.degree b = 3 := by
    rcases hdeg b with h2 | h3
    · exact (hlow hBb hB2 h2).elim
    · exact h3
  have hx3 : G.degree x = 3 := by
    rcases hdeg x with h2 | h3
    · exact (hlow hsx hs2 h2).elim
    · exact h3
  have hy3 : G.degree y = 3 := by
    rcases hdeg y with h2 | h3
    · exact (hlow hty ht2 h2).elim
    · exact h3
  obtain ⟨l,m,hlm,hlz,hmz,hpl,hpm,hplms⟩ := forward_pair hzp hp3
  obtain ⟨k,d,hkd,hkA,hdA,hak,had,hakds⟩ := forward_pair hAa ha3
  obtain ⟨e,f,hef,heB,hfB,hbe,hbf,hbefs⟩ := forward_pair hBb hb3
  let v : Fin 19 → V := ![r,c,w,z,A,B,s,t,p,a,b,x,y,l,m,k,d,e,f]
  have hv : Function.Surjective v := by
    intro u
    have hu : u ∈ sideTree G r c ∪ sideTree G c r := by rw [hcover]; simp
    simp only [sideTree,Finset.mem_union,Finset.mem_singleton] at hu
    rcases hu with (((hu | hu) | hu) | hu) | (((hu | hu) | hu) | hu)
    · exact ⟨0,hu.symm⟩
    · simp only [armLevelOne,hrwz,Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with hu | hu
      · exact ⟨2,hu.symm⟩
      · exact ⟨3,hu.symm⟩
    · obtain ⟨j,hj,hu⟩ := arm_level_two_spec hu
      rw [hrwz] at hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · rw [hwst] at hu
        simp only [Finset.mem_insert,Finset.mem_singleton] at hu
        rcases hu with hu | hu
        · exact ⟨6,hu.symm⟩
        · exact ⟨7,hu.symm⟩
      · rw [hzps] at hu
        exact ⟨8,(Finset.mem_singleton.mp hu).symm⟩
    · obtain ⟨j,k0,hj,hk0,hu⟩ := arm_level_three_spec hu
      rw [hrwz] at hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · rw [hwst] at hk0
        simp only [Finset.mem_insert,Finset.mem_singleton] at hk0
        rcases hk0 with rfl | rfl
        · rw [hsxs] at hu
          exact ⟨11,(Finset.mem_singleton.mp hu).symm⟩
        · rw [htys] at hu
          exact ⟨12,(Finset.mem_singleton.mp hu).symm⟩
      · rw [hzps] at hk0
        have heq := Finset.mem_singleton.mp hk0
        subst k0
        rw [hplms] at hu
        simp only [Finset.mem_insert,Finset.mem_singleton] at hu
        rcases hu with hu | hu
        · exact ⟨13,hu.symm⟩
        · exact ⟨14,hu.symm⟩
    · exact ⟨1,hu.symm⟩
    · simp only [armLevelOne,hcAB,Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with hu | hu
      · exact ⟨4,hu.symm⟩
      · exact ⟨5,hu.symm⟩
    · obtain ⟨j,hj,hu⟩ := arm_level_two_spec hu
      rw [hcAB] at hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · rw [hAas] at hu
        exact ⟨9,(Finset.mem_singleton.mp hu).symm⟩
      · rw [hBbs] at hu
        exact ⟨10,(Finset.mem_singleton.mp hu).symm⟩
    · obtain ⟨j,k0,hj,hk0,hu⟩ := arm_level_three_spec hu
      rw [hcAB] at hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · rw [hAas] at hk0
        have heq := Finset.mem_singleton.mp hk0
        subst k0
        rw [hakds] at hu
        simp only [Finset.mem_insert,Finset.mem_singleton] at hu
        rcases hu with hu | hu
        · exact ⟨15,hu.symm⟩
        · exact ⟨16,hu.symm⟩
      · rw [hBbs] at hk0
        have heq := Finset.mem_singleton.mp hk0
        subst k0
        rw [hbefs] at hu
        simp only [Finset.mem_insert,Finset.mem_singleton] at hu
        rcases hu with hu | hu
        · exact ⟨17,hu.symm⟩
        · exact ⟨18,hu.symm⟩
  have hinj : Function.Injective v :=
    ((Fintype.bijective_iff_surjective_and_card v).mpr ⟨hv,by simpa using hN.symm⟩).1
  refine ⟨v,hinj,rfl,rfl,rfl,?_,hx3,hy3⟩
  intro i
  fin_cases i
  · convert hrwz using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hcAB using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hwst using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hzps using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hAas using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hBbs using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hsxs using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert htys using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hplms using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hakds using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _
  · convert hbefs using 1 <;> ext u <;> simp [v,treeParent,treeChildren]
    all_goals intro _; exact G.mem_neighborFinset _ _





private theorem high_edge_neighbor_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hcover : L ∪ R = Finset.univ)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hN : Fintype.card V = 19)
    {r c : V} (hrc : G.Adj r c) (hr : G.degree r = 3) (hc : G.degree c = 3) :
    (degreeThree G (G.neighborFinset r)).card +
      (degreeThree G (G.neighborFinset c)).card ≤ 3 := by
  have hk {a b : V} (hab : G.Adj a b) (hb : G.degree b = 3) :
      (degreeThree G (armLevelOne G a b)).card + 1 =
        (degreeThree G (G.neighborFinset a)).card := by
    have he : degreeThree G (armLevelOne G a b) =
        (degreeThree G (G.neighborFinset a)).erase b := by
      ext x
      simp [degreeThree,armLevelOne,and_assoc,and_left_comm]
    rw [he]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hab,hb⟩)
  have hrk := hk hrc hc
  have hck := hk hrc.symm hr
  have horient : r ∈ L ∨ r ∈ R := by
    rw [← Finset.mem_union,hcover]
    exact Finset.mem_univ _
  rcases horient with hL | hR
  · have hh := double_root_sharp hpart hg hdeg hlow hL hrc hr hc
    omega
  · have hh := double_root_sharp hpart.symm hg hdeg hlow hR hrc hr hc
    omega


end D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSlice
