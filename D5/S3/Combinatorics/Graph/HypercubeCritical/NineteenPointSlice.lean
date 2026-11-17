/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSlice
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Actual balanced cubic Q9 slices of size at most nineteen reconstruct Gray support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeFiveNeighborGap
import Batteries.Tactic.OpenPrivate

/-! The equality tree at nineteen points and its cubical matching obstruction. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSlice

attribute [local simp] decide_eq_true_eq Finset.filter_insert Finset.filter_singleton

private def leafRow : Fin 4 → Fin 19 := ![11,12,13,14]
private def leafCol : Fin 4 → Fin 19 := ![15,16,17,18]
private def rowParent : Fin 4 → Fin 19 := ![6,7,8,8]
private def colParent : Fin 4 → Fin 19 := ![9,9,10,10]
private def rowCount (e : Fin 4 → Fin 4 → Bool) (i : Fin 4) : ℕ :=
  (Finset.univ.filter (fun j => e i j)).card
private def colCount (e : Fin 4 → Fin 4 → Bool) (j : Fin 4) : ℕ :=
  (Finset.univ.filter (fun i => e i j)).card

private def leafOrder (s a b : Bool) : Fin 4 → Fin 4 :=
  if s then ![if b then 3 else 2,if b then 2 else 3,if a then 1 else 0,if a then 0 else 1]
  else ![if a then 1 else 0,if a then 0 else 1,if b then 3 else 2,if b then 2 else 3]

-- This certificate chooses only four right leaves; it classifies no graphs.
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
set_option maxSynthPendingDepth 1024 in
private theorem leaf_choices :
    ∀ (X Y : Fin 4 → Bool) (c e : Fin 4),
      (∀ j, X j = true ∨ Y j = true) →
      (∀ j, ¬ (X j = true ∧ Y j = true)) →
      (∀ j k, j ≠ k → colParent j = colParent k →
        ¬ (X j = true ∧ X k = true) ∧ ¬ (Y j = true ∧ Y k = true)) →
      c ≠ e → colParent c ≠ colParent e →
      ¬ (X c = true ∧ X e = true) → ¬ (Y c = true ∧ Y e = true) →
      ∃ s a b t : Bool,
        (∀ j, X (leafOrder s a b j) = (![true,false,false,true] j)) ∧
        (∀ j, Y (leafOrder s a b j) = (![false,true,true,false] j)) ∧
        (if t then e else c) = leafOrder s a b 0 ∧
        (if t then c else e) = leafOrder s a b 2 := by
  intro X Y c e hc hd hp hce hcp hnx hny
  have hY (j : Fin 4) : Y j = !(X j) := by
    have hcj := hc j
    have hdj := hd j
    cases hx : X j <;> cases hy : Y j <;> simp_all
  fin_cases c <;> fin_cases e <;> norm_num [colParent] at hcp
  all_goals
    cases hx0 : X 0 <;> cases hx1 : X 1 <;>
      cases hx2 : X 2 <;> cases hx3 : X 3
  all_goals
    have hy0 := hY 0
    have hy1 := hY 1
    have hy2 := hY 2
    have hy3 := hY 3
    simp only [hx0,hx1,hx2,hx3,Bool.not_false,Bool.not_true] at hy0 hy1 hy2 hy3
    simp [Fin.forall_fin_succ,colParent,hx0,hx1,hx2,hx3,hy0,hy1,hy2,hy3] at hp hnx hny
    all_goals simp only [Bool.exists_bool]
    all_goals simp [leafOrder,Fin.forall_fin_succ,hx0,hx1,hx2,hx3,hy0,hy1,hy2,hy3]


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

-- Only the three distance bounds occur here; bridge degrees are irrelevant.
private theorem three_matching_centers {p O : Q 9}
    (d : Bool × Fin 3 → Fin 9) (hd : Function.Injective d)
    (hnear : ∀ i, (diff p (flip (flip O (d (false, i))) (d (true, i)))).card ≤ 2) :
    p = O := by
  let D := diff p O
  let P (i : Fin 3) : Finset (Fin 9) := {d (false, i), d (true, i)}
  have hp (i : Fin 3) : (diff (flip (flip O (d (false, i))) (d (true, i))) O) = P i := by
    rw [diff_symm]
    exact diff_double O (fun h => Bool.noConfusion (congrArg Prod.fst (hd h)))
  have hc (i : Fin 3) : (P i).card = 2 := by
    have hn : d (false, i) ≠ d (true, i) := fun h =>
      Bool.noConfusion (congrArg Prod.fst (hd h))
    simp [P, hn]
  have hb (i : Fin 3) : D.card ≤ 2 * (D ∩ P i).card := by
    have ht := diff_triangle_card p (flip (flip O (d (false, i))) (d (true, i))) O
    rw [hp i, hc i] at ht
    have hn := hnear i
    change D.card ≤ 2 * (D ∩ P i).card
    change (diff p (flip (flip O (d (false, i))) (d (true, i)))).card +
      2 * (D ∩ P i).card = D.card + 2 at ht
    omega
  have hdis (i j : Fin 3) (hij : i ≠ j) : Disjoint (D ∩ P i) (D ∩ P j) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have hk' := (Finset.mem_inter.mp hk).2
    have hl' := (Finset.mem_inter.mp hl).2
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hk' hl'
    rcases hk' with h | h <;> rcases hl' with h' | h'
    all_goals exact hij (congrArg Prod.snd (hd (h.symm.trans h')))
  have hbound : (D ∩ P 0).card + (D ∩ P 1).card + (D ∩ P 2).card ≤ D.card := by
    calc
      _ = ((D ∩ P 0) ∪ (D ∩ P 1) ∪ (D ∩ P 2)).card := by
        rw [Finset.card_union_of_disjoint
          (Finset.disjoint_union_left.mpr ⟨hdis 0 2 (by decide), hdis 1 2 (by decide)⟩),
          Finset.card_union_of_disjoint (hdis 0 1 (by decide))]
      _ ≤ D.card := Finset.card_le_card (by
        intro k hk
        rcases Finset.mem_union.mp hk with hk | hk
        · rcases Finset.mem_union.mp hk with hk | hk
          · exact (Finset.mem_inter.mp hk).1
          · exact (Finset.mem_inter.mp hk).1
        · exact (Finset.mem_inter.mp hk).1)
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have hzero : D.card = 0 := by omega
  exact (diff_empty_iff p O).mp (Finset.card_eq_zero.mp hzero)

private theorem labelled_matching_obstruction {S K : Finset (Q 9)}
    (hKS : K ⊆ S)
    (l : Labels ((hypercube 9).induce (K : Set (Q 9))))
    (p : (S : Set (Q 9)))
    (hdeg : ((hypercube 9).induce (S : Set (Q 9))).degree p ≤ 3)
    (hnear : ∀ i, (diff p.val ((Labels.M l) i i).val).card ≤ 2) : False := by
  obtain ⟨d,hd,ha,hb,hm⟩ := normal_labels l
  let O := flip ((Labels.A l) 0).val (d (false, 0))
  have hp : p.val = O := three_matching_centers d hd (fun i => by
    simpa only [hm, CubicalSubdivisionRigidity.gridMiddle,
      CubicalSubdivisionRigidity.gridHigh] using hnear i)
  let f (h : Bool × Fin 3) : (S : Set (Q 9)) :=
    ⟨(if h.1 then (Labels.B l) h.2 else (Labels.A l) h.2).val,
      hKS (if h.1 then (Labels.B l) h.2 else (Labels.A l) h.2).property⟩
  have hf : Function.Injective f := by
    intro h h' he
    have hvv : (if h.1 then (Labels.B l) h.2 else (Labels.A l) h.2).val =
        (if h'.1 then (Labels.B l) h'.2 else (Labels.A l) h'.2).val :=
      congrArg (fun v : (S : Set (Q 9)) => v.val) he
    exact (Labels.high_inj l) (Subtype.ext hvv)
  have hv (h : Bool × Fin 3) : (f h).val = flip O (d h) := by
    rcases h with ⟨s,i⟩
    cases s
    · exact ha i
    · exact hb i
  have hs : Finset.univ.image f ⊆
      (((hypercube 9).induce (S : Set (Q 9))).neighborFinset p) := by
    intro v h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
    change (hypercube 9).Adj p.val (f j).val
    rw [hp,hv]
    exact flip_adj O (d j)
  have hh := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hf,Finset.card_univ,
    SimpleGraph.card_neighborFinset_eq_degree] at hh
  norm_num at hh
  omega


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

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
private theorem fork_leaf_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hg : (8 : ℕ∞) ≤ G.egirth)
    (v : Fin 19 → V) (hv : Function.Injective v) (hsurj : Function.Surjective v)
    (hroot : G.Adj (v 0) (v 1))
    (htree : ∀ i : Fin 11,
      (G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i))).erase
        (v (treeParent i)) = (treeChildren i).image v) :
    (∀ i : Fin 11, ∀ j : Fin 19,
      G.Adj (v (Fin.castLE (by decide : 11 ≤ 19) i)) (v j) ↔
        j ∈ insert (treeParent i) (treeChildren i)) ∧
    (∀ i, G.neighborFinset (v (leafRow i)) =
      insert (v (rowParent i))
        ((Finset.univ.filter (fun j => G.Adj (v (leafRow i)) (v (leafCol j)))).image
          (fun j => v (leafCol j)))) ∧
    (∀ j, G.neighborFinset (v (leafCol j)) =
      insert (v (colParent j))
        ((Finset.univ.filter (fun i => G.Adj (v (leafRow i)) (v (leafCol j)))).image
          (fun i => v (leafRow i)))) ∧
    (∀ j, ¬ (G.Adj (v 11) (v (leafCol j)) ∧ G.Adj (v 12) (v (leafCol j)))) ∧
    (∀ (i : Fin 2) (j k : Fin 4), j ≠ k → colParent j = colParent k →
      ¬ (G.Adj (v (leafRow (Fin.castLE (by decide : 2 ≤ 4) i))) (v (leafCol j)) ∧
         G.Adj (v (leafRow (Fin.castLE (by decide : 2 ≤ 4) i))) (v (leafCol k)))) := by
  have hchild (i : Fin 11) (j : Fin 19) (hj : j ∈ treeChildren i) :
      G.Adj (v (Fin.castLE (by decide : 11 ≤ 19) i)) (v j) := by
    apply (G.mem_neighborFinset _ _).mp
    apply (Finset.mem_erase.mp (show v j ∈
      (G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i))).erase
        (v (treeParent i)) from ?_)).2
    rw [htree]
    exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
  have hpar (i : Fin 11) : G.Adj (v (Fin.castLE (by decide : 11 ≤ 19) i))
      (v (treeParent i)) := by
    fin_cases i
    · exact hroot
    · exact hroot.symm
    · exact (hchild 0 2 (by decide)).symm
    · exact (hchild 0 3 (by decide)).symm
    · exact (hchild 1 4 (by decide)).symm
    · exact (hchild 1 5 (by decide)).symm
    · exact (hchild 2 6 (by decide)).symm
    · exact (hchild 2 7 (by decide)).symm
    · exact (hchild 3 8 (by decide)).symm
    · exact (hchild 4 9 (by decide)).symm
    · exact (hchild 5 10 (by decide)).symm
  have hfixed (i : Fin 11) (j : Fin 19) :
      G.Adj (v (Fin.castLE (by decide : 11 ≤ 19) i)) (v j) ↔
        j ∈ insert (treeParent i) (treeChildren i) := by
    have hp := (G.mem_neighborFinset _ _).mpr (hpar i)
    have hn : G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i)) =
        (insert (treeParent i) (treeChildren i)).image v := by
      rw [← Finset.insert_erase hp,htree,Finset.image_insert]
    rw [← G.mem_neighborFinset,hn]
    simp [Finset.mem_image,hv.eq_iff]
  have hf0 (j : Fin 19) : G.Adj (v 0) (v j) ↔ j ∈ ({1,2,3} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 0 j
  have hr0 (j : Fin 19) : G.Adj (v j) (v 0) ↔ j ∈ ({1,2,3} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf0 j)
  have hf1 (j : Fin 19) : G.Adj (v 1) (v j) ↔ j ∈ ({0,4,5} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 1 j
  have hr1 (j : Fin 19) : G.Adj (v j) (v 1) ↔ j ∈ ({0,4,5} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf1 j)
  have hf2 (j : Fin 19) : G.Adj (v 2) (v j) ↔ j ∈ ({0,6,7} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 2 j
  have hr2 (j : Fin 19) : G.Adj (v j) (v 2) ↔ j ∈ ({0,6,7} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf2 j)
  have hf3 (j : Fin 19) : G.Adj (v 3) (v j) ↔ j ∈ ({0,8} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 3 j
  have hr3 (j : Fin 19) : G.Adj (v j) (v 3) ↔ j ∈ ({0,8} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf3 j)
  have hf4 (j : Fin 19) : G.Adj (v 4) (v j) ↔ j ∈ ({1,9} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 4 j
  have hr4 (j : Fin 19) : G.Adj (v j) (v 4) ↔ j ∈ ({1,9} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf4 j)
  have hf5 (j : Fin 19) : G.Adj (v 5) (v j) ↔ j ∈ ({1,10} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 5 j
  have hr5 (j : Fin 19) : G.Adj (v j) (v 5) ↔ j ∈ ({1,10} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf5 j)
  have hf6 (j : Fin 19) : G.Adj (v 6) (v j) ↔ j ∈ ({2,11} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 6 j
  have hr6 (j : Fin 19) : G.Adj (v j) (v 6) ↔ j ∈ ({2,11} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf6 j)
  have hf7 (j : Fin 19) : G.Adj (v 7) (v j) ↔ j ∈ ({2,12} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 7 j
  have hr7 (j : Fin 19) : G.Adj (v j) (v 7) ↔ j ∈ ({2,12} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf7 j)
  have hf8 (j : Fin 19) : G.Adj (v 8) (v j) ↔ j ∈ ({3,13,14} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 8 j
  have hr8 (j : Fin 19) : G.Adj (v j) (v 8) ↔ j ∈ ({3,13,14} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf8 j)
  have hf9 (j : Fin 19) : G.Adj (v 9) (v j) ↔ j ∈ ({4,15,16} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 9 j
  have hr9 (j : Fin 19) : G.Adj (v j) (v 9) ↔ j ∈ ({4,15,16} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf9 j)
  have hf10 (j : Fin 19) : G.Adj (v 10) (v j) ↔ j ∈ ({5,17,18} : Finset (Fin 19)) := by
    simpa [treeParent,treeChildren] using hfixed 10 j
  have hr10 (j : Fin 19) : G.Adj (v j) (v 10) ↔ j ∈ ({5,17,18} : Finset (Fin 19)) :=
    (G.adj_comm _ _).trans (hf10 j)
  have he0_2 : G.Adj (v 0) (v 2) := hchild 0 2 (by decide)
  have he0_3 : G.Adj (v 0) (v 3) := hchild 0 3 (by decide)
  have he1_4 : G.Adj (v 1) (v 4) := hchild 1 4 (by decide)
  have he1_5 : G.Adj (v 1) (v 5) := hchild 1 5 (by decide)
  have he2_6 : G.Adj (v 2) (v 6) := hchild 2 6 (by decide)
  have he2_7 : G.Adj (v 2) (v 7) := hchild 2 7 (by decide)
  have he3_8 : G.Adj (v 3) (v 8) := hchild 3 8 (by decide)
  have he4_9 : G.Adj (v 4) (v 9) := hchild 4 9 (by decide)
  have he5_10 : G.Adj (v 5) (v 10) := hchild 5 10 (by decide)
  have he6_11 : G.Adj (v 6) (v 11) := hchild 6 11 (by decide)
  have he7_12 : G.Adj (v 7) (v 12) := hchild 7 12 (by decide)
  have he8_13 : G.Adj (v 8) (v 13) := hchild 8 13 (by decide)
  have he8_14 : G.Adj (v 8) (v 14) := hchild 8 14 (by decide)
  have he9_15 : G.Adj (v 9) (v 15) := hchild 9 15 (by decide)
  have he9_16 : G.Adj (v 9) (v 16) := hchild 9 16 (by decide)
  have he10_17 : G.Adj (v 10) (v 17) := hchild 10 17 (by decide)
  have he10_18 : G.Adj (v 10) (v 18) := hchild 10 18 (by decide)
  have hn11_12 : ¬ G.Adj (v 11) (v 12) := by
    intro hab
    let p : G.Walk (v 11) (v 12) := Walk.cons he6_11.symm (Walk.cons he2_6.symm (Walk.cons he2_7 (Walk.cons he7_12 (Walk.nil))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn12_11 : ¬ G.Adj (v 12) (v 11) := fun h => hn11_12 h.symm
  have hn11_13 : ¬ G.Adj (v 11) (v 13) := by
    intro hab
    let p : G.Walk (v 11) (v 13) := Walk.cons he6_11.symm (Walk.cons he2_6.symm (Walk.cons he0_2.symm (Walk.cons he0_3 (Walk.cons he3_8 (Walk.cons he8_13 (Walk.nil))))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn13_11 : ¬ G.Adj (v 13) (v 11) := fun h => hn11_13 h.symm
  have hn11_14 : ¬ G.Adj (v 11) (v 14) := by
    intro hab
    let p : G.Walk (v 11) (v 14) := Walk.cons he6_11.symm (Walk.cons he2_6.symm (Walk.cons he0_2.symm (Walk.cons he0_3 (Walk.cons he3_8 (Walk.cons he8_14 (Walk.nil))))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn14_11 : ¬ G.Adj (v 14) (v 11) := fun h => hn11_14 h.symm
  have hn12_13 : ¬ G.Adj (v 12) (v 13) := by
    intro hab
    let p : G.Walk (v 12) (v 13) := Walk.cons he7_12.symm (Walk.cons he2_7.symm (Walk.cons he0_2.symm (Walk.cons he0_3 (Walk.cons he3_8 (Walk.cons he8_13 (Walk.nil))))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn13_12 : ¬ G.Adj (v 13) (v 12) := fun h => hn12_13 h.symm
  have hn12_14 : ¬ G.Adj (v 12) (v 14) := by
    intro hab
    let p : G.Walk (v 12) (v 14) := Walk.cons he7_12.symm (Walk.cons he2_7.symm (Walk.cons he0_2.symm (Walk.cons he0_3 (Walk.cons he3_8 (Walk.cons he8_14 (Walk.nil))))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn14_12 : ¬ G.Adj (v 14) (v 12) := fun h => hn12_14 h.symm
  have hn13_14 : ¬ G.Adj (v 13) (v 14) := by
    intro hab
    let p : G.Walk (v 13) (v 14) := Walk.cons he8_13.symm (Walk.cons he8_14 (Walk.nil))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn14_13 : ¬ G.Adj (v 14) (v 13) := fun h => hn13_14 h.symm
  have hn15_16 : ¬ G.Adj (v 15) (v 16) := by
    intro hab
    let p : G.Walk (v 15) (v 16) := Walk.cons he9_15.symm (Walk.cons he9_16 (Walk.nil))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn16_15 : ¬ G.Adj (v 16) (v 15) := fun h => hn15_16 h.symm
  have hn15_17 : ¬ G.Adj (v 15) (v 17) := by
    intro hab
    let p : G.Walk (v 15) (v 17) := Walk.cons he9_15.symm (Walk.cons he4_9.symm (Walk.cons he1_4.symm (Walk.cons he1_5 (Walk.cons he5_10 (Walk.cons he10_17 (Walk.nil))))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn17_15 : ¬ G.Adj (v 17) (v 15) := fun h => hn15_17 h.symm
  have hn15_18 : ¬ G.Adj (v 15) (v 18) := by
    intro hab
    let p : G.Walk (v 15) (v 18) := Walk.cons he9_15.symm (Walk.cons he4_9.symm (Walk.cons he1_4.symm (Walk.cons he1_5 (Walk.cons he5_10 (Walk.cons he10_18 (Walk.nil))))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn18_15 : ¬ G.Adj (v 18) (v 15) := fun h => hn15_18 h.symm
  have hn16_17 : ¬ G.Adj (v 16) (v 17) := by
    intro hab
    let p : G.Walk (v 16) (v 17) := Walk.cons he9_16.symm (Walk.cons he4_9.symm (Walk.cons he1_4.symm (Walk.cons he1_5 (Walk.cons he5_10 (Walk.cons he10_17 (Walk.nil))))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn17_16 : ¬ G.Adj (v 17) (v 16) := fun h => hn16_17 h.symm
  have hn16_18 : ¬ G.Adj (v 16) (v 18) := by
    intro hab
    let p : G.Walk (v 16) (v 18) := Walk.cons he9_16.symm (Walk.cons he4_9.symm (Walk.cons he1_4.symm (Walk.cons he1_5 (Walk.cons he5_10 (Walk.cons he10_18 (Walk.nil))))))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn18_16 : ¬ G.Adj (v 18) (v 16) := fun h => hn16_18 h.symm
  have hn17_18 : ¬ G.Adj (v 17) (v 18) := by
    intro hab
    let p : G.Walk (v 17) (v 18) := Walk.cons he10_17.symm (Walk.cons he10_18 (Walk.nil))
    have hp : p.IsPath := by
      simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have heq := short_paths_unique_seven hg hp
      (show (Walk.cons hab Walk.nil).IsPath by simp [hv.eq_iff]) (by simp [p])
    have hl := congrArg Walk.length heq
    norm_num [p] at hl
  have hn18_17 : ¬ G.Adj (v 18) (v 17) := fun h => hn17_18 h.symm
  refine ⟨hfixed,?_,?_,?_,?_⟩
  · intro i
    ext z
    obtain ⟨j,rfl⟩ := hsurj z
    simp only [G.mem_neighborFinset,Finset.mem_insert,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    fin_cases i <;> fin_cases j <;>
      simp [leafRow,leafCol,rowParent,colParent,Fin.forall_fin_succ,Fin.exists_fin_succ,
        SimpleGraph.mem_neighborFinset,Finset.mem_image,hv.eq_iff,hf0,hf1,hf2,hf3,hf4,hf5,hf6,hf7,hf8,hf9,hf10,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hr9,hr10,hn11_12,hn11_13,hn11_14,hn12_11,hn12_13,hn12_14,hn13_11,hn13_12,hn13_14,hn14_11,hn14_12,hn14_13,hn15_16,hn15_17,hn15_18,hn16_15,hn16_17,hn16_18,hn17_15,hn17_16,hn17_18,hn18_15,hn18_16,hn18_17] <;> exact G.adj_comm _ _
  · intro i
    ext z
    obtain ⟨j,rfl⟩ := hsurj z
    simp only [G.mem_neighborFinset,Finset.mem_insert,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    fin_cases i <;> fin_cases j <;>
      simp [leafRow,leafCol,rowParent,colParent,Fin.forall_fin_succ,Fin.exists_fin_succ,
        SimpleGraph.mem_neighborFinset,Finset.mem_image,hv.eq_iff,hf0,hf1,hf2,hf3,hf4,hf5,hf6,hf7,hf8,hf9,hf10,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hr9,hr10,hn11_12,hn11_13,hn11_14,hn12_11,hn12_13,hn12_14,hn13_11,hn13_12,hn13_14,hn14_11,hn14_12,hn14_13,hn15_16,hn15_17,hn15_18,hn16_15,hn16_17,hn16_18,hn17_15,hn17_16,hn17_18,hn18_15,hn18_16,hn18_17] <;> exact G.adj_comm _ _
  · intro j ⟨hj,hk⟩
    let p : G.Walk (v 11) (v 12) := Walk.cons he6_11.symm
      (Walk.cons he2_6.symm (Walk.cons he2_7 (Walk.cons he7_12 Walk.nil)))
    let q : G.Walk (v 11) (v 12) := Walk.cons hj (Walk.cons hk.symm Walk.nil)
    have hp : p.IsPath := by simp [p,Walk.cons_isPath_iff,hv.eq_iff]
    have hq : q.IsPath := by
      apply Walk.IsPath.mk'
      change [v 11,v (leafCol j),v 12].Nodup
      fin_cases j <;> simp [hv.eq_iff,leafCol]
    have heq := short_paths_unique_seven hg hp hq (by simp [p,q])
    have hl := congrArg Walk.length heq
    norm_num [p,q] at hl
  · intro i j k hjk hpk ⟨hij,hik⟩
    have hjp : G.Adj (v (colParent j)) (v (leafCol j)) := by
      fin_cases j
      · exact he9_15
      · exact he9_16
      · exact he10_17
      · exact he10_18
    have hkp : G.Adj (v (colParent j)) (v (leafCol k)) := by
      rw [hpk]
      fin_cases k
      · exact he9_15
      · exact he9_16
      · exact he10_17
      · exact he10_18
    let p : G.Walk (v (leafCol j)) (v (leafCol k)) :=
      Walk.cons hjp.symm (Walk.cons hkp Walk.nil)
    let q : G.Walk (v (leafCol j)) (v (leafCol k)) :=
      Walk.cons hij.symm (Walk.cons hik Walk.nil)
    have hne : v (leafCol j) ≠ v (leafCol k) := by
      intro h
      have he := hv h
      have hinj : Function.Injective leafCol := by decide
      exact hjk (hinj he)
    have hp : p.IsPath := by
      apply Walk.IsPath.mk'
      simp [p,G.ne_of_adj hkp,(G.ne_of_adj hjp).symm,hne]
    have hq : q.IsPath := by
      apply Walk.IsPath.mk'
      simp [q,G.ne_of_adj hik,(G.ne_of_adj hij).symm,hne]
    have heq := short_paths_unique_seven hg hp hq (by simp [p,q])
    have hs := congrArg Walk.support heq
    have hbad : v (colParent j) = v (leafRow (Fin.castLE (by decide : 2 ≤ 4) i)) := by
      simpa [p,q] using hs
    have he := hv hbad
    fin_cases i <;> fin_cases j <;> simp [colParent,leafRow] at he


set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
private theorem fork_leaf_singletons
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ z, G.degree z = 2 ∨ G.degree z = 3)
    (v : Fin 19 → V) (hv : Function.Injective v) (hsurj : Function.Surjective v)
    (hroot : G.Adj (v 0) (v 1))
    (htree : ∀ i : Fin 11,
      (G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i))).erase
        (v (treeParent i)) = (treeChildren i).image v)
    (hx : G.degree (v 11) = 3) (hy : G.degree (v 12) = 3)
    (hsum : ∑ i : Fin 19, G.degree (v i) = 48) :
    ∃ c e : Fin 4,
      G.neighborFinset (v 13) = {v 8,v (leafCol c)} ∧
      G.neighborFinset (v 14) = {v 8,v (leafCol e)} ∧
      G.degree (v 13) = 2 ∧ G.degree (v 14) = 2 ∧
      c ≠ e ∧
      (∀ j, G.degree (v (leafCol j)) = 3 ↔ j = c ∨ j = e) ∧
      (∀ j, G.Adj (v 11) (v (leafCol j)) ∨ G.Adj (v 12) (v (leafCol j))) ∧
      (Finset.univ.filter (fun j => G.Adj (v 11) (v (leafCol j)))).card = 2 ∧
      (Finset.univ.filter (fun j => G.Adj (v 12) (v (leafCol j)))).card = 2 := by
  obtain ⟨hfix,hrow,hcol,hncommon,hnpair⟩ := fork_leaf_incidence hg v hv hsurj hroot htree
  let E (i j : Fin 4) : Bool := decide (G.Adj (v (leafRow i)) (v (leafCol j)))
  have hE (i j : Fin 4) : E i j = true ↔ G.Adj (v (leafRow i)) (v (leafCol j)) := by
    exact decide_eq_true_iff

  have hrinj : Function.Injective (fun i => v (leafRow i)) := hv.comp (by decide)
  have hcinj : Function.Injective (fun j => v (leafCol j)) := hv.comp (by decide)
  have hrd (i : Fin 4) : G.degree (v (leafRow i)) = 1 + rowCount E i := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,hrow,
      Finset.card_insert_of_notMem,Finset.card_image_of_injective _ hcinj]
    · simp [rowCount,hE,Nat.add_comm]
    · simp only [Finset.mem_image]
      rintro ⟨j,_,he⟩
      have hn : ∀ i j, leafCol j ≠ rowParent i := by decide
      exact hn i j (hv he)
  have hcd (j : Fin 4) : G.degree (v (leafCol j)) = 1 + colCount E j := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,hcol,
      Finset.card_insert_of_notMem,Finset.card_image_of_injective _ hrinj]
    · simp [colCount,E,Nat.add_comm]
    · simp only [Finset.mem_image]
      rintro ⟨i,_,he⟩
      have hn : ∀ i j, leafRow i ≠ colParent j := by decide
      exact hn i j (hv he)
  have hni (i : Fin 11) : G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i)) =
      (insert (treeParent i) (treeChildren i)).image v := by
    ext z
    obtain ⟨j,rfl⟩ := hsurj z
    simp [G.mem_neighborFinset,hfix,Finset.mem_image,hv.eq_iff]
  have hdi (i : Fin 11) : G.degree (v (Fin.castLE (by decide : 11 ≤ 19) i)) =
      (insert (treeParent i) (treeChildren i)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,hni,Finset.card_image_of_injective _ hv]
  have hd0 : G.degree (v 0) = 3 := by simpa [treeParent,treeChildren] using hdi 0
  have hd1 : G.degree (v 1) = 3 := by simpa [treeParent,treeChildren] using hdi 1
  have hd2 : G.degree (v 2) = 3 := by simpa [treeParent,treeChildren] using hdi 2
  have hd3 : G.degree (v 3) = 2 := by simpa [treeParent,treeChildren] using hdi 3
  have hd4 : G.degree (v 4) = 2 := by simpa [treeParent,treeChildren] using hdi 4
  have hd5 : G.degree (v 5) = 2 := by simpa [treeParent,treeChildren] using hdi 5
  have hd6 : G.degree (v 6) = 2 := by simpa [treeParent,treeChildren] using hdi 6
  have hd7 : G.degree (v 7) = 2 := by simpa [treeParent,treeChildren] using hdi 7
  have hd8 : G.degree (v 8) = 3 := by simpa [treeParent,treeChildren] using hdi 8
  have hd9 : G.degree (v 9) = 3 := by simpa [treeParent,treeChildren] using hdi 9
  have hd10 : G.degree (v 10) = 3 := by simpa [treeParent,treeChildren] using hdi 10
  have hrr0 : G.degree (v 11) = 1 + rowCount E 0 := hrd 0
  have hcc0 : G.degree (v 15) = 1 + colCount E 0 := hcd 0
  have hrr1 : G.degree (v 12) = 1 + rowCount E 1 := hrd 1
  have hcc1 : G.degree (v 16) = 1 + colCount E 1 := hcd 1
  have hrr2 : G.degree (v 13) = 1 + rowCount E 2 := hrd 2
  have hcc2 : G.degree (v 17) = 1 + colCount E 2 := hcd 2
  have hrr3 : G.degree (v 14) = 1 + rowCount E 3 := hrd 3
  have hcc3 : G.degree (v 18) = 1 + colCount E 3 := hcd 3
  have hc0 : rowCount E 0 = 2 := by omega
  have hc1 : rowCount E 1 = 2 := by omega
  have hc2 : 1 ≤ rowCount E 2 := by
    have hh := hdeg (v 13)
    omega
  have hc3 : 1 ≤ rowCount E 3 := by
    have hh := hdeg (v 14)
    omega
  have hrcsum : ∑ i : Fin 4, rowCount E i = ∑ j : Fin 4, colCount E j := by
    simp only [rowCount,colCount,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hu4 : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  have hu19 : (Finset.univ : Finset (Fin 19)) =
    {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18} := by decide
  norm_num [hu4,hu19] at hrcsum hsum
  rw [hd0,hd1,hd2,hd3,hd4,hd5,hd6,hd7,hd8,hd9,hd10,hrr0,hrr1,hrr2,hrr3,hcc0,hcc1,hcc2,hcc3] at hsum
  have hr2 : rowCount E 2 = 1 := by omega
  have hr3 : rowCount E 3 = 1 := by omega
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp (show
      (Finset.univ.filter (fun j => G.Adj (v 13) (v (leafCol j)))).card = 1 by
    simpa [rowCount,hE,leafRow] using hr2)
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp (show
      (Finset.univ.filter (fun j => G.Adj (v 14) (v (leafCol j)))).card = 1 by
    simpa [rowCount,hE,leafRow] using hr3)
  have hfc (j : Fin 4) : G.Adj (v 13) (v (leafCol j)) ↔ j = c := by
    have hh := congrArg (fun T : Finset (Fin 4) => j ∈ T) hc
    simpa using Iff.of_eq hh
  have hfe (j : Fin 4) : G.Adj (v 14) (v (leafCol j)) ↔ j = e := by
    have hh := congrArg (fun T : Finset (Fin 4) => j ∈ T) he
    simpa using Iff.of_eq hh
  have hl : G.neighborFinset (v 13) = {v 8,v (leafCol c)} := by
    apply Finset.ext
    intro z
    change z ∈ G.neighborFinset (v (leafRow 2)) ↔ _
    rw [hrow]
    simp [leafRow,rowParent,Finset.mem_image,hfc,eq_comm]
  have hm : G.neighborFinset (v 14) = {v 8,v (leafCol e)} := by
    apply Finset.ext
    intro z
    change z ∈ G.neighborFinset (v (leafRow 3)) ↔ _
    rw [hrow]
    simp [leafRow,rowParent,Finset.mem_image,hfe,eq_comm]
  have hcover : ∀ j, G.Adj (v 11) (v (leafCol j)) ∨ G.Adj (v 12) (v (leafCol j)) := by
    have hdis : Disjoint (Finset.univ.filter (fun j => E 0 j))
        (Finset.univ.filter (fun j => E 1 j)) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      exact hncommon j ⟨by simpa [hE,leafRow] using (Finset.mem_filter.mp hj).2,
        by simpa [hE,leafRow] using (Finset.mem_filter.mp hk).2⟩
    have heq : (Finset.univ.filter (fun j => E 0 j)) ∪
        (Finset.univ.filter (fun j => E 1 j)) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hdis]
      change 4 ≤ rowCount E 0 + rowCount E 1
      omega
    intro j
    have hj : j ∈ (Finset.univ.filter (fun j => E 0 j)) ∪
        (Finset.univ.filter (fun j => E 1 j)) := by rw [heq]; simp
    simpa [hE,leafRow] using hj
  have hce : c ≠ e := by
    intro h
    have hc' : G.Adj (v 13) (v (leafCol c)) := by
      apply (G.mem_neighborFinset _ _).mp
      rw [hl]; simp
    have he' : G.Adj (v 14) (v (leafCol c)) := by
      apply (G.mem_neighborFinset _ _).mp
      rw [hm,h]; simp
    have hcl : E 2 c = true := by simpa [hE,leafRow] using hc'
    have hel : E 3 c = true := by simpa [hE,leafRow] using he'
    have hh := hcd c
    have hd := hdeg (v (leafCol c))
    rcases hcover c with ha | ha
    · have hca : E 0 c = true := by simpa [hE,leafRow] using ha
      have hcount : 3 ≤ colCount E c := by
        by_cases hb : E 1 c = true <;> simp [colCount,hu4,hcl,hel,hca,hb]
      omega
    · have hca : E 1 c = true := by simpa [hE,leafRow] using ha
      have hcount : 3 ≤ colCount E c := by
        by_cases hb : E 0 c = true <;> simp [colCount,hu4,hcl,hel,hca,hb]
      omega
  have hhigh (j : Fin 4) : G.degree (v (leafCol j)) = 3 ↔ j = c ∨ j = e := by
    have hs2 (j : Fin 4) : G.Adj (v 13) (v (leafCol j)) ↔ j = c := by
      have hm : j ∈ Finset.univ.filter (fun j => G.Adj (v 13) (v (leafCol j))) ↔ j = c := by
        rw [hc]; simp
      simpa using hm
    have hs3 (j : Fin 4) : G.Adj (v 14) (v (leafCol j)) ↔ j = e := by
      have hm : j ∈ Finset.univ.filter (fun j => G.Adj (v 14) (v (leafCol j))) ↔ j = e := by
        rw [he]; simp
      simpa using hm
    have hcard : colCount E j = 1 + (if j = c then 1 else 0) + (if j = e then 1 else 0) := by
      have h01 : (if G.Adj (v 11) (v (leafCol j)) then 1 else 0) +
          (if G.Adj (v 12) (v (leafCol j)) then 1 else 0) = (1 : ℕ) := by
        rcases hcover j with hh | hh
        · have hn : ¬ G.Adj (v 12) (v (leafCol j)) := fun h => hncommon j ⟨hh,h⟩
          simp only [hh,hn,ite_true,ite_false]
        · have hn : ¬ G.Adj (v 11) (v (leafCol j)) := fun h => hncommon j ⟨h,hh⟩
          simp only [hh,hn,ite_true,ite_false]
      unfold colCount
      rw [Finset.card_eq_sum_ones,Finset.sum_filter]
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
      simp [hE,leafRow,hs2,hs3]
      omega
    rw [hcd,hcard]
    by_cases hjc : j = c <;> by_cases hje : j = e <;> simp_all
  exact ⟨c,e,hl,hm,by omega,by omega,hce,hhigh,hcover,
    by simpa [rowCount,hE,leafRow] using hc0,by simpa [rowCount,hE,leafRow] using hc1⟩

set_option maxHeartbeats 4000000 in
private theorem fork_leaf_choices
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hg : (8 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ z, G.degree z = 2 ∨ G.degree z = 3)
    (v : Fin 19 → V) (hv : Function.Injective v) (hsurj : Function.Surjective v)
    (hroot : G.Adj (v 0) (v 1))
    (htree : ∀ i : Fin 11,
      (G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i))).erase
        (v (treeParent i)) = (treeChildren i).image v)
    (hx : G.degree (v 11) = 3) (hy : G.degree (v 12) = 3)
    (hsum : ∑ i : Fin 19, G.degree (v i) = 48)
    (hJ : ∀ {z w}, G.Adj z w → G.degree z = 3 → G.degree w = 3 →
      (degreeThree G (G.neighborFinset z)).card +
        (degreeThree G (G.neighborFinset w)).card ≤ 3) :
    ∃ s a b t : Bool,
      (∀ j, G.Adj (v 11) (v (leafCol (leafOrder s a b j))) ↔
        ![true,false,false,true] j = true) ∧
      (∀ j, G.Adj (v 12) (v (leafCol (leafOrder s a b j))) ↔
        ![false,true,true,false] j = true) ∧
      G.neighborFinset (v (if t then 14 else 13)) = {v 8,v (leafCol (leafOrder s a b 0))} ∧
      G.neighborFinset (v (if t then 13 else 14)) = {v 8,v (leafCol (leafOrder s a b 2))} := by
  obtain ⟨hfix,hrow,hcol,hncommon,hnpair⟩ := fork_leaf_incidence hg v hv hsurj hroot htree
  obtain ⟨c,e,hl,hm,hl2,hm2,hce,hhigh,hcover,hXcard,hYcard⟩ :=
    fork_leaf_singletons hg hdeg v hv hsurj hroot htree hx hy hsum
  have hpHigh (j : Fin 4) : G.degree (v (colParent j)) = 3 := by
    have hni (i : Fin 11) : G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i)) =
        (insert (treeParent i) (treeChildren i)).image v := by
      ext z
      obtain ⟨k,rfl⟩ := hsurj z
      simp [G.mem_neighborFinset,hfix,Finset.mem_image,hv.eq_iff]
    have hdi (i : Fin 11) : G.degree (v (Fin.castLE (by decide : 11 ≤ 19) i)) =
        (insert (treeParent i) (treeChildren i)).card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,hni,Finset.card_image_of_injective _ hv]
    have h9 : G.degree (v 9) = 3 := by simpa [treeParent,treeChildren] using hdi 9
    have h10 : G.degree (v 10) = 3 := by simpa [treeParent,treeChildren] using hdi 10
    have hp : colParent j = 9 ∨ colParent j = 10 := by fin_cases j <;> decide
    rcases hp with hp | hp
    · rw [hp]; exact h9
    · rw [hp]; exact h10
  have hpEdge (j : Fin 4) : G.Adj (v (colParent j)) (v (leafCol j)) := by
    apply Adj.symm
    rw [← G.mem_neighborFinset,hcol]; simp
  have hcHigh : G.degree (v (leafCol c)) = 3 := (hhigh c).mpr (Or.inl rfl)
  have heHigh : G.degree (v (leafCol e)) = 3 := (hhigh e).mpr (Or.inr rfl)
  have hne : v (leafCol c) ≠ v (leafCol e) := by
    intro h
    have hi : Function.Injective leafCol := by decide
    exact hce (hi (hv h))
  have htwo {z a b : V} (hza : G.Adj z a) (hzb : G.Adj z b)
      (hab : a ≠ b) (ha : G.degree a = 3) (hb : G.degree b = 3) :
      2 ≤ (degreeThree G (G.neighborFinset z)).card := by
    have hs : ({a,b} : Finset V) ⊆ degreeThree G (G.neighborFinset z) := by
      simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,degreeThree,
        G.mem_neighborFinset,hza,hzb,ha,hb]
    have hh := Finset.card_le_card hs
    simpa [hab] using hh
  have hcTwo : 2 ≤ (degreeThree G (G.neighborFinset (v (leafCol c)))).card := by
    rcases hcover c with ha | ha
    · apply htwo (hpEdge c).symm ha.symm _ (hpHigh c) hx
      intro h
      have heq := hv h
      fin_cases c <;> simp [colParent] at heq
    · apply htwo (hpEdge c).symm ha.symm _ (hpHigh c) hy
      intro h
      have heq := hv h
      fin_cases c <;> simp [colParent] at heq
  have hcp : colParent c ≠ colParent e := by
    intro heq
    have h2 := htwo (hpEdge c) (show G.Adj (v (colParent c)) (v (leafCol e)) by
      rw [heq]; exact hpEdge e) hne hcHigh heHigh
    have h3 := hJ (hpEdge c) (hpHigh c) hcHigh
    omega
  have hnx : ¬ (G.Adj (v 11) (v (leafCol c)) ∧ G.Adj (v 11) (v (leafCol e))) := by
    rintro ⟨ha,hb⟩
    have h2 := htwo ha hb hne hcHigh heHigh
    have h3 := hJ ha hx hcHigh
    omega
  have hny : ¬ (G.Adj (v 12) (v (leafCol c)) ∧ G.Adj (v 12) (v (leafCol e))) := by
    rintro ⟨ha,hb⟩
    have h2 := htwo ha hb hne hcHigh heHigh
    have h3 := hJ ha hy hcHigh
    omega
  let X (j : Fin 4) : Bool := decide (G.Adj (v 11) (v (leafCol j)))
  let Y (j : Fin 4) : Bool := decide (G.Adj (v 12) (v (leafCol j)))
  obtain ⟨s,a,b,t,hX,hY,hcN,heN⟩ := leaf_choices X Y c e
    (by simpa [X,Y] using hcover)
    (by simpa [X,Y] using hncommon)
    (by
      intro j k hjk hpar
      exact ⟨by simpa [X,leafRow] using hnpair 0 j k hjk hpar,
        by simpa [Y,leafRow] using hnpair 1 j k hjk hpar⟩)
    hce hcp (by simpa [X] using hnx) (by simpa [Y] using hny)
  refine ⟨s,a,b,t,?_,?_,?_,?_⟩
  · intro j
    simpa [X] using (show X (leafOrder s a b j) = true ↔
      ![true,false,false,true] j = true by rw [hX])
  · intro j
    simpa [Y] using (show Y (leafOrder s a b j) = true ↔
      ![false,true,true,false] j = true by rw [hY])
  · cases t
    · simpa using hl.trans (by rw [← hcN]; rfl)
    · simpa using hm.trans (by rw [← hcN]; rfl)
  · cases t
    · simpa using hm.trans (by rw [← heN]; rfl)
    · simpa using hl.trans (by rw [← heN]; rfl)

private def matchA : Fin 3 → Fin 19 := ![1,12,11]
private def matchB : Fin 3 → Fin 19 := ![2,10,9]
private def matchM : Fin 3 → Fin 3 → Fin 19 := ![![0,5,4],![7,17,16],![6,18,15]]
private def matchBridge : Fin 3 → Fin 19 := ![3,14,13]
private def matchSelected : Finset (Fin 19) := {0,1,2,4,5,6,7,9,10,11,12,15,16,17,18}
private def matchNeighbors : Fin 3 → Fin 3 → Finset (Fin 19) :=
  ![![{1,2,3},{1,10},{1,9}],![{2,12},{10,12,14},{9,12}],![{2,11},{10,11},{9,11,13}]]

set_option maxHeartbeats 4000000 in
private theorem matching_configuration {S : Finset (Q 9)}
    (v : Fin 19 → (S : Set (Q 9))) (hv : Function.Injective v)
    (hmid : ∀ i j,
      (((hypercube 9).induce (S : Set (Q 9))).neighborFinset (v (matchM i j))) =
        (matchNeighbors i j).image v)
    (hb : ∀ i, (hypercube 9).Adj (v 8).val (v (matchBridge i)).val ∧
      (hypercube 9).Adj (v (matchBridge i)).val (v (matchM i i)).val) :
    ∃ K : Finset (Q 9), K ⊆ S ∧
      ∃ l : Labels ((hypercube 9).induce (K : Set (Q 9))),
        ∀ i, (diff (v 8).val ((Labels.M l) i i).val).card ≤ 2 := by
  let K := matchSelected.image (fun i => (v i).val)
  have hKS : K ⊆ S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact (v i).property
  have hmem (i : Fin 19) (hi : i ∈ matchSelected) : (v i).val ∈ K :=
    Finset.mem_image.mpr ⟨i,hi,rfl⟩
  let A (i : Fin 3) : (K : Set (Q 9)) :=
    ⟨(v (matchA i)).val,hmem _ (by fin_cases i <;> decide)⟩
  let B (j : Fin 3) : (K : Set (Q 9)) :=
    ⟨(v (matchB j)).val,hmem _ (by fin_cases j <;> decide)⟩
  let M (i j : Fin 3) : (K : Set (Q 9)) :=
    ⟨(v (matchM i j)).val,hmem _ (by fin_cases i <;> fin_cases j <;> decide)⟩
  have hval : Function.Injective (fun i => (v i).val) := by
    intro i j h
    exact hv (Subtype.ext h)
  let l : Labels ((hypercube 9).induce (K : Set (Q 9))) := Labels.mk A B M
    (by
      intro i j he
      have hi : Function.Injective (fun q : Bool × Fin 3 => if q.1 then matchB q.2 else matchA q.2) := by decide
      apply hi
      apply hval
      have hh := congrArg (fun x : (K : Set (Q 9)) => x.val) he
      rcases i with ⟨s,i⟩
      rcases j with ⟨t,j⟩
      cases s <;> cases t <;> simpa [A,B] using hh )
    (by
      intro i j z
      obtain ⟨k,hk,hz⟩ := Finset.mem_image.mp z.property
      have he : (v k).val = z.val := hz
      have ht : k ∈ matchNeighbors i j ↔ k = matchA i ∨ k = matchB j := by
        have htrim : ∀ (i j : Fin 3) (k : Fin 19), k ∈ matchSelected →
            (k ∈ matchNeighbors i j ↔ k = matchA i ∨ k = matchB j) := by decide
        exact htrim i j k hk
      have ha : (hypercube 9).Adj (v (matchM i j)).val z.val ↔ k ∈ matchNeighbors i j := by
        rw [← he]
        change ((hypercube 9).induce (S : Set (Q 9))).Adj (v (matchM i j)) (v k) ↔ _
        rw [← SimpleGraph.mem_neighborFinset,hmid]
        simp [Finset.mem_image,hv.eq_iff]
      change (hypercube 9).Adj (v (matchM i j)).val z.val ↔ z = A i ∨ z = B j
      rw [ha,ht]
      simp [Subtype.ext_iff,A,B,← he,hval.eq_iff] )
    (by
      intro i j k he
      have hh := hval (congrArg (fun x : (K : Set (Q 9)) => x.val) he)
      have hi : ∀ i, Function.Injective (matchM i) := by decide
      exact hi i hh )
    (by
      intro j i k he
      have hh := hval (congrArg (fun x : (K : Set (Q 9)) => x.val) he)
      have hi : ∀ j, Function.Injective (fun i => matchM i j) := by decide
      exact hi j hh )
    (by
      intro z
      obtain ⟨k,hk,hz⟩ := Finset.mem_image.mp z.property
      have hc : (∃ i, k = matchA i) ∨ (∃ j, k = matchB j) ∨ ∃ i j, k = matchM i j := by
        have hc : ∀ k ∈ matchSelected,
            (∃ i, k = matchA i) ∨ (∃ j, k = matchB j) ∨ ∃ i j, k = matchM i j := by decide
        exact hc k hk
      rcases hc with ⟨i,rfl⟩ | ⟨j,rfl⟩ | ⟨i,j,rfl⟩
      · exact Or.inl ⟨i,Subtype.ext hz.symm⟩
      · exact Or.inr (Or.inl ⟨j,Subtype.ext hz.symm⟩)
      · exact Or.inr (Or.inr ⟨i,j,Subtype.ext hz.symm⟩) )
  refine ⟨K,hKS,l,?_⟩
  intro i
  have h1 : (diff (v 8).val (v (matchBridge i)).val).card = 1 := (hb i).1
  have h2 : (diff (v (matchM i i)).val (v (matchBridge i)).val).card = 1 :=
    (hb i).2.symm
  have ht := diff_triangle_card (v 8).val (v (matchM i i)).val (v (matchBridge i)).val
  change (diff (v 8).val (v (matchM i i)).val).card ≤ 2
  omega

private def forkOrder (s a b t : Bool) : Fin 19 → Fin 19 :=
  ![0,1,2,3,cond s 5 4,cond s 4 5,6,7,8,cond s 10 9,cond s 9 10,11,12,
    cond t 14 13,cond t 13 14,
    leafCol (leafOrder s a b 0),leafCol (leafOrder s a b 1),
    leafCol (leafOrder s a b 2),leafCol (leafOrder s a b 3)]

set_option maxHeartbeats 6000000 in
set_option linter.unusedSimpArgs false in
private theorem fork_matching_configuration {S : Finset (Q 9)}
    (v : Fin 19 → (S : Set (Q 9))) (hv : Function.Injective v)
    (hsurj : Function.Surjective v)
    (hg : (8 : ℕ∞) ≤ ((hypercube 9).induce (S : Set (Q 9))).egirth)
    (hdeg : ∀ z, ((hypercube 9).induce (S : Set (Q 9))).degree z = 2 ∨
      ((hypercube 9).induce (S : Set (Q 9))).degree z = 3)
    (hroot : ((hypercube 9).induce (S : Set (Q 9))).Adj (v 0) (v 1))
    (htree : ∀ i : Fin 11,
      (((hypercube 9).induce (S : Set (Q 9))).neighborFinset
        (v (Fin.castLE (by decide : 11 ≤ 19) i))).erase
        (v (treeParent i)) = (treeChildren i).image v)
    (hx : ((hypercube 9).induce (S : Set (Q 9))).degree (v 11) = 3)
    (hy : ((hypercube 9).induce (S : Set (Q 9))).degree (v 12) = 3)
    (hsum : ∑ i : Fin 19, ((hypercube 9).induce (S : Set (Q 9))).degree (v i) = 48)
    (hJ : ∀ {z w}, ((hypercube 9).induce (S : Set (Q 9))).Adj z w →
      ((hypercube 9).induce (S : Set (Q 9))).degree z = 3 →
      ((hypercube 9).induce (S : Set (Q 9))).degree w = 3 →
      (degreeThree ((hypercube 9).induce (S : Set (Q 9)))
        (((hypercube 9).induce (S : Set (Q 9))).neighborFinset z)).card +
      (degreeThree ((hypercube 9).induce (S : Set (Q 9)))
        (((hypercube 9).induce (S : Set (Q 9))).neighborFinset w)).card ≤ 3) :
    ∃ K : Finset (Q 9), K ⊆ S ∧
      ∃ l : Labels ((hypercube 9).induce (K : Set (Q 9))),
        ∀ i, (diff (v 8).val ((Labels.M l) i i).val).card ≤ 2 := by
  obtain ⟨hfix,hrow,hcol,hncommon,hnpair⟩ := fork_leaf_incidence hg v hv hsurj hroot htree
  obtain ⟨s,a,b,t,hX,hY,hL,hM⟩ := fork_leaf_choices hg hdeg v hv hsurj hroot htree hx hy hsum hJ
  let σ := leafOrder s a b
  let W (i : Fin 19) := v (forkOrder s a b t i)
  have hσ : Function.Injective σ := by cases s <;> cases a <;> cases b <;> decide
  have hcinj : Function.Injective (fun j => v (leafCol (σ j))) :=
    hv.comp ((show Function.Injective leafCol by decide).comp hσ)
  have h8ne (j : Fin 4) : v (leafCol (σ j)) ≠ v 8 := by
    intro h
    have hn : ∀ j, leafCol j ≠ (8 : Fin 19) := by decide
    exact hn _ (hv h)
  have hfix' (i : Fin 11) (k : Fin 19) :
      (hypercube 9).Adj (v (Fin.castLE (by decide : 11 ≤ 19) i)).val (v k).val ↔
        k ∈ insert (treeParent i) (treeChildren i) := hfix i k
  change (∀ j, (hypercube 9).Adj (v 11).val (v (leafCol (σ j))).val ↔
    ![true,false,false,true] j = true) at hX
  change (∀ j, (hypercube 9).Adj (v 12).val (v (leafCol (σ j))).val ↔
    ![false,true,true,false] j = true) at hY
  change ((hypercube 9).induce (S : Set (Q 9))).neighborFinset
    (v (if t then 14 else 13)) = {v 8,v (leafCol (σ 0))} at hL
  change ((hypercube 9).induce (S : Set (Q 9))).neighborFinset
    (v (if t then 13 else 14)) = {v 8,v (leafCol (σ 2))} at hM
  have hLAdj (j : Fin 4) :
      (hypercube 9).Adj (v (if t then 14 else 13)).val (v (leafCol (σ j))).val ↔ j = 0 := by
    have hh := congrArg (fun T => v (leafCol (σ j)) ∈ T) hL
    simpa [SimpleGraph.mem_neighborFinset,h8ne,hcinj.eq_iff] using Iff.of_eq hh
  have hMAdj (j : Fin 4) :
      (hypercube 9).Adj (v (if t then 13 else 14)).val (v (leafCol (σ j))).val ↔ j = 2 := by
    have hh := congrArg (fun T => v (leafCol (σ j)) ∈ T) hM
    simpa [SimpleGraph.mem_neighborFinset,h8ne,hcinj.eq_iff] using Iff.of_eq hh
  have h13 (j : Fin 4) :
      (hypercube 9).Adj (v 13).val (v (leafCol (σ j))).val ↔
        j = (if t then 2 else 0) := by
    cases t
    · simpa using hLAdj j
    · simpa using hMAdj j
  have h14 (j : Fin 4) :
      (hypercube 9).Adj (v 14).val (v (leafCol (σ j))).val ↔
        j = (if t then 0 else 2) := by
    cases t
    · simpa using hMAdj j
    · simpa using hLAdj j
  have hcN (j : Fin 4) (k : Fin 19) :
      (hypercube 9).Adj (v (leafCol (σ j))).val (v k).val ↔
      k ∈ (![({colParent (σ 0),11,if t then 14 else 13} : Finset (Fin 19)),
         {colParent (σ 1),12},{colParent (σ 2),12,if t then 13 else 14},
         {colParent (σ 3),11}] j) := by
    have hh := congrArg (fun T => v k ∈ T) (hcol (σ j))
    cases t <;> fin_cases j <;>
      simpa [SimpleGraph.mem_neighborFinset,Finset.mem_image,Fin.exists_fin_succ,
        leafRow,hv.eq_iff,hX,hY,h13,h14,eq_comm] using Iff.of_eq hh
  have hmid (i j : Fin 3) :
      ((hypercube 9).induce (S : Set (Q 9))).neighborFinset (W (matchM i j)) =
        (matchNeighbors i j).image W := by
    apply Finset.ext
    intro z
    obtain ⟨k,rfl⟩ := hsurj z
    rw [SimpleGraph.mem_neighborFinset]
    change (hypercube 9).Adj (W (matchM i j)).val (v k).val ↔ _
    fin_cases i <;> fin_cases j
    · cases s <;> cases a <;> cases b <;> cases t <;>
        simpa [W,forkOrder,leafOrder,leafCol,colParent,σ,matchM,matchNeighbors,
          treeParent,treeChildren,SimpleGraph.mem_neighborFinset,Finset.mem_image,
          hv.eq_iff,eq_comm] using hfix' 0 k
    · cases s
      · simpa [W,forkOrder,matchM,matchNeighbors,treeParent,treeChildren,
          SimpleGraph.mem_neighborFinset,Finset.mem_image,hv.eq_iff,eq_comm] using hfix' 5 k
      · simpa [W,forkOrder,matchM,matchNeighbors,treeParent,treeChildren,
          SimpleGraph.mem_neighborFinset,Finset.mem_image,hv.eq_iff,eq_comm] using hfix' 4 k
    · cases s
      · simpa [W,forkOrder,matchM,matchNeighbors,treeParent,treeChildren,
          SimpleGraph.mem_neighborFinset,Finset.mem_image,hv.eq_iff,eq_comm] using hfix' 4 k
      · simpa [W,forkOrder,matchM,matchNeighbors,treeParent,treeChildren,
          SimpleGraph.mem_neighborFinset,Finset.mem_image,hv.eq_iff,eq_comm] using hfix' 5 k
    · cases s <;> cases a <;> cases b <;> cases t <;>
        simpa [W,forkOrder,leafOrder,leafCol,colParent,σ,matchM,matchNeighbors,
          treeParent,treeChildren,SimpleGraph.mem_neighborFinset,Finset.mem_image,
          hv.eq_iff,eq_comm] using hfix' 7 k
    · cases s <;> cases a <;> cases b <;> cases t <;>
        simpa [W,forkOrder,leafOrder,leafCol,colParent,σ,matchM,matchNeighbors,
          treeParent,treeChildren,SimpleGraph.mem_neighborFinset,Finset.mem_image,
          hv.eq_iff,eq_comm] using hcN 2 k
    · cases s <;> cases a <;> cases b <;> cases t <;>
        simpa [W,forkOrder,leafOrder,leafCol,colParent,σ,matchM,matchNeighbors,
          treeParent,treeChildren,SimpleGraph.mem_neighborFinset,Finset.mem_image,
          hv.eq_iff,eq_comm] using hcN 1 k
    · cases s <;> cases a <;> cases b <;> cases t <;>
        simpa [W,forkOrder,leafOrder,leafCol,colParent,σ,matchM,matchNeighbors,
          treeParent,treeChildren,SimpleGraph.mem_neighborFinset,Finset.mem_image,
          hv.eq_iff,eq_comm] using hfix' 6 k
    · cases s <;> cases a <;> cases b <;> cases t <;>
        simpa [W,forkOrder,leafOrder,leafCol,colParent,σ,matchM,matchNeighbors,
          treeParent,treeChildren,SimpleGraph.mem_neighborFinset,Finset.mem_image,
          hv.eq_iff,eq_comm] using hcN 3 k
    · cases s <;> cases a <;> cases b <;> cases t <;>
        simpa [W,forkOrder,leafOrder,leafCol,colParent,σ,matchM,matchNeighbors,
          treeParent,treeChildren,SimpleGraph.mem_neighborFinset,Finset.mem_image,
          hv.eq_iff,eq_comm] using hcN 0 k
  have hwi : Function.Injective W := hv.comp (by
    cases s <;> cases a <;> cases b <;> cases t <;> decide)
  have hb (i : Fin 3) : (hypercube 9).Adj (W 8).val (W (matchBridge i)).val ∧
      (hypercube 9).Adj (W (matchBridge i)).val (W (matchM i i)).val := by
    have h0 : (hypercube 9).Adj (v 8).val (v 3).val := (hfix' 8 3).mpr (by decide)
    have h1 : (hypercube 9).Adj (v 3).val (v 0).val := (hfix' 3 0).mpr (by decide)
    have hL0 : (hypercube 9).Adj (v (if t then 14 else 13)).val (v 8).val := by
      have hh := (Iff.of_eq (congrArg (fun T => v 8 ∈ T) hL)).mpr (by simp)
      exact (((hypercube 9).induce (S : Set (Q 9))).mem_neighborFinset _ _).mp hh
    have hLc : (hypercube 9).Adj (v (if t then 14 else 13)).val (v (leafCol (σ 0))).val := by
      have hh := (Iff.of_eq (congrArg (fun T => v (leafCol (σ 0)) ∈ T) hL)).mpr (by simp [σ])
      exact (((hypercube 9).induce (S : Set (Q 9))).mem_neighborFinset _ _).mp hh
    have hM0 : (hypercube 9).Adj (v (if t then 13 else 14)).val (v 8).val := by
      have hh := (Iff.of_eq (congrArg (fun T => v 8 ∈ T) hM)).mpr (by simp)
      exact (((hypercube 9).induce (S : Set (Q 9))).mem_neighborFinset _ _).mp hh
    have hMe : (hypercube 9).Adj (v (if t then 13 else 14)).val (v (leafCol (σ 2))).val := by
      have hh := (Iff.of_eq (congrArg (fun T => v (leafCol (σ 2)) ∈ T) hM)).mpr (by simp [σ])
      exact (((hypercube 9).induce (S : Set (Q 9))).mem_neighborFinset _ _).mp hh
    fin_cases i
    · exact ⟨h0,h1⟩
    · simpa [W,forkOrder,matchBridge,matchM,σ,Bool.cond_eq_ite] using And.intro hM0.symm hMe
    · simpa [W,forkOrder,matchBridge,matchM,σ,Bool.cond_eq_ite] using And.intro hL0.symm hLc
  simpa [W,forkOrder] using matching_configuration W hwi hmid hb

-- Sum transport is consumed with the actual degree function.
private theorem nineteen_label_count
    {V : Type*} [Fintype V]
    (hN : Fintype.card V = 19) (v : Fin 19 → V) (hv : Function.Injective v)
    (f : V → ℕ) (hf : ∑ z, f z = 48) :
    Function.Surjective v ∧ ∑ i : Fin 19, f (v i) = 48 := by
  have hsurj : Function.Surjective v :=
    ((Fintype.bijective_iff_injective_and_card v).mpr ⟨hv,by simpa using hN.symm⟩).2
  exact ⟨hsurj,(show Function.Bijective v from ⟨hv,hsurj⟩).sum_comp f |>.trans hf⟩

-- The finite equality-tree construction is elaborated within the actual slice.
set_option maxHeartbeats 2000000 in
/-- The slice bound is on the original actual coordinate-zero half. Both
concluding equivalences act on the entire cube and all nine coordinates. -/
theorem nineteen_point_slice_gray_reconstruction {C : Finset (Q 9)} (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card ≤ 19) :
    ∃ (g : Q 9 ≃ Q 9) (pi : Fin 9 ≃ Fin 9),
      (∀ x i, g (BalancedCriticalSpectrum.flip x i) =
        BalancedCriticalSpectrum.flip (g x) (pi i)) ∧
      C = (GrayGridComponent.support 3).image g := by
  by_cases hs18 : (coordinateSlice C b).card ≤ 18
  · exact EighteenPointSlice.eighteen_point_slice_gray_reconstruction hC hr hb b hs18
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 := fun v =>
    coordinate_slice_degree_cases v.property hr
  have hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False := by
    intro v w hxy hx hy
    exact coordinate_slice_low_independent hr hb hxy hx hy
  have hbal : IsBalanced S := balanced_subset hb (Finset.filter_subset _ _)
  have hg : (8 : ℕ∞) ≤ G.egirth := BalancedCubeGirth.eight_le_egirth S hbal
  have hqcard : (degreeTwo G Finset.univ).card = directionEdges C 0 := low_slice_card_eq_q hr
  have h54 : 54 ≤ C.card := by
    by_contra hn
    exact BalancedCubeFiftyFourLowerBound.result ⟨C,hC,hr,hb,by omega⟩
  have h6 : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hScard : Fintype.card (S : Set (Q 9)) = S.card := by simp
  have hN : Fintype.card (S : Set (Q 9)) = 19 := by
    rw [hScard]
    change (coordinateSlice C b).card = 19
    omega
  have hp := parts_card G hdeg Finset.univ
  have hi := twice_low_le_three_high G hdeg hlow
  have hsum : 2 * (degreeTwo G Finset.univ).card +
      3 * (degreeThree G Finset.univ).card = 2 * G.edgeFinset.card := by
    rw [← sum_degrees_parts G hdeg Finset.univ]
    exact G.sum_degrees_eq_twice_card_edges
  rw [Finset.card_univ] at hp
  have hcases : (degreeTwo G Finset.univ).card = 9 ∨
      (degreeTwo G Finset.univ).card = 11 := by omega
  have hpart := parity_bipartite S
  have hcover := parity_union S
  have horient (r : (S : Set (Q 9))) :
      r ∈ paritySide S false ∨ r ∈ paritySide S true := by
    rw [← Finset.mem_union,hcover]
    exact Finset.mem_univ _
  exfalso
  rcases hcases with hq9 | hq11
  · have hh10 : (degreeThree G Finset.univ).card = 10 := by omega
    obtain ⟨r,c,w,hr3,hc3,hw3,hrc,hrw,hcw⟩ := high_fork_exists G hdeg hq9 hh10
    have htree : ∃ v : Fin 19 → (S : Set (Q 9)), Function.Injective v ∧
        v 0 = r ∧ v 1 = c ∧ v 2 = w ∧
        (∀ i : Fin 11, (G.neighborFinset (v (Fin.castLE (by decide : 11 ≤ 19) i))).erase
          (v (treeParent i)) = (treeChildren i).image v) ∧
        G.degree (v 11) = 3 ∧ G.degree (v 12) = 3 := by
      rcases horient r with hrL | hrR
      · exact fork_tree_vertices hpart hg hdeg hlow hrL hrc hrw hcw hr3 hc3 hw3 hN
      · exact fork_tree_vertices hpart.symm hg hdeg hlow hrR hrc hrw hcw hr3 hc3 hw3 hN
    obtain ⟨v,hv,hr0,hc1,hw2,htree,hx3,hy3⟩ := htree
    have hJ : ∀ {a d : (S : Set (Q 9))}, G.Adj a d → G.degree a = 3 → G.degree d = 3 →
        (degreeThree G (G.neighborFinset a)).card +
          (degreeThree G (G.neighborFinset d)).card ≤ 3 :=
      fun had ha hd => high_edge_neighbor_bound hpart hcover hg hdeg hlow hN had ha hd
    have hconfiguration : ∃ K : Finset (Q 9), K ⊆ S ∧
        ∃ l : Labels ((hypercube 9).induce (K : Set (Q 9))),
          ∀ i, (diff (v 8).val ((Labels.M l) i i).val).card ≤ 2 := by
      have htotal := sum_degrees_parts G hdeg Finset.univ
      norm_num only [hq9,hh10] at htotal
      obtain ⟨hsurj,hdsum⟩ := nineteen_label_count hN v hv (fun z => G.degree z) htotal
      exact fork_matching_configuration v hv hsurj hg hdeg
        (by simpa only [hr0,hc1] using hrc) htree hx3 hy3 hdsum hJ
    obtain ⟨K,hKS,l,hnear⟩ := hconfiguration
    have hdp : G.degree (v 8) ≤ 3 := by
      rcases hdeg (v 8) with h | h <;> omega
    exact labelled_matching_obstruction hKS l (v 8) hdp hnear
  · have hstrict : 2 * (degreeTwo G Finset.univ).card <
        3 * (degreeThree G Finset.univ).card := by omega
    obtain ⟨r,c,hrc,hr3,hc3⟩ := high_edge_exists G hdeg hstrict
    rcases horient r with hrL | hrR
    · exact eleven_low_nineteen_impossible hpart hg hdeg hlow hrL hrc hr3 hc3 hN hq11
    · exact eleven_low_nineteen_impossible hpart.symm hg hdeg hlow hrR hrc hr3 hc3 hN hq11


#print axioms nineteen_point_slice_gray_reconstruction
#print axioms fork_matching_configuration
#print axioms three_matching_centers
#print axioms labelled_matching_obstruction
#print axioms eleven_low_nineteen_impossible
#print axioms fork_equality_tree
#print axioms fork_tree_vertices
#print axioms high_edge_neighbor_bound

end D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSlice
