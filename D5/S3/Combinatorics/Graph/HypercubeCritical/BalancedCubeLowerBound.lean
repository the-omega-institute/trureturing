/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Actual coordinate slices of balanced cubic cube restrictions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
import Batteries.Tactic.OpenPrivate

/-! Actual coordinate slices inherit balance and lose precisely their crossing edge. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

open scoped BigOperators Classical
open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip_adj flip_flip IsBalanced directionEdges
  direction_edge_count)
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open GirthSliceCounting (degreeTwo degreeThree)
open private degree_parts_union degree_parts_disjoint sum_degree_parts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

abbrev Cube9 := Q 9

/-- The coordinate-zero slices of the actual selected vertices. -/
def coordinateSlice (C : Finset Cube9) (b : Bool) : Finset Cube9 :=
  C.filter (fun x => x 0 = b)

private theorem balanced_subset {n : Nat} {C S : Finset (Q n)}
    (hC : IsBalanced C) (hSC : S ⊆ C) : IsBalanced S := by
  obtain ⟨sigma, hs⟩ := hC
  exact ⟨sigma, (fun x hx => hs.1 x (hSC hx)),
    fun x hx y hy hxy => hs.2 x (hSC hx) y (hSC hy) hxy⟩

private theorem direction_edge_count_zero {C : Finset Cube9}
    (hr : ((hypercube 9).induce (C : Set Cube9)).IsRegularOfDegree 3)
    (hb : IsBalanced C) : 6 * directionEdges C 0 = C.card := by
  simpa using (direction_edge_count (d := 3) C hr hb 0)

private theorem direction_edges_pos {C : Finset Cube9} (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set Cube9)).IsRegularOfDegree 3)
    (hb : IsBalanced C) : 0 < directionEdges C 0 := by
  have h := direction_edge_count_zero hr hb
  have hc := hC.card_pos
  omega

private theorem coordinate_slices_partition (C : Finset Cube9) :
    coordinateSlice C false ∪ coordinateSlice C true = C := by
  ext x
  cases hx : x 0 <;> simp [coordinateSlice, hx]

private theorem coordinate_slices_disjoint (C : Finset Cube9) :
    Disjoint (coordinateSlice C false) (coordinateSlice C true) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Bool.false_ne_true ((Finset.mem_filter.mp hx).2.symm.trans
    (Finset.mem_filter.mp hy).2)

private theorem coordinate_slice_card_sum (C : Finset Cube9) :
    (coordinateSlice C false).card + (coordinateSlice C true).card = C.card := by
  rw [← Finset.card_union_of_disjoint (coordinate_slices_disjoint C),
    coordinate_slices_partition]

private theorem coordinate_slice_smaller (C : Finset Cube9) :
    ∃ b : Bool, 2 * (coordinateSlice C b).card ≤ C.card := by
  have hs := coordinate_slice_card_sum C
  by_cases h : (coordinateSlice C false).card ≤ (coordinateSlice C true).card
  · exact ⟨false, by omega⟩
  · exact ⟨true, by omega⟩

private theorem cross_not_slice {C : Finset Cube9} {b : Bool} {x : Cube9}
    (hx : x ∈ coordinateSlice C b) : BalancedCriticalSpectrum.flip x 0 ∉ coordinateSlice C b := by
  intro h
  have hb := (Finset.mem_filter.mp h).2
  have hx0 := (Finset.mem_filter.mp hx).2
  cases b <;> simp [BalancedCriticalSpectrum.flip, hx0] at hb

private theorem adjacent_slice_or_cross {C : Finset Cube9} {b : Bool}
    {x y : Cube9} (hx : x ∈ coordinateSlice C b) (hyC : y ∈ C)
    (hxy : (hypercube 9).Adj x y) :
    y ∈ coordinateSlice C b ∨ y = BalancedCriticalSpectrum.flip x 0 := by
  have hx0 := (Finset.mem_filter.mp hx).2
  obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
  by_cases hi : i = 0
  · exact Or.inr (by rw [hi])
  · exact Or.inl (Finset.mem_filter.mpr ⟨hyC, by
      simpa [BalancedCriticalSpectrum.flip, Ne.symm hi] using hx0⟩)

private theorem neighbor_inter_slice {C : Finset Cube9} {b : Bool} {x : Cube9}
    (hx : x ∈ coordinateSlice C b) :
    (hypercube 9).neighborFinset x ∩ C =
      ((hypercube 9).neighborFinset x ∩ coordinateSlice C b) ∪
        (if BalancedCriticalSpectrum.flip x 0 ∈ C then {BalancedCriticalSpectrum.flip x 0} else ∅) := by
  by_cases hc : BalancedCriticalSpectrum.flip x 0 ∈ C
  · simp only [hc, ite_true]
    ext y
    constructor
    · intro hy
      obtain ⟨hyN, hyC⟩ := Finset.mem_inter.mp hy
      rcases adjacent_slice_or_cross hx hyC
          (((hypercube 9).mem_neighborFinset _ _).mp hyN) with hys | rfl
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hyN, hys⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨hyN, hyS⟩ := Finset.mem_inter.mp hy
        exact Finset.mem_inter.mpr ⟨hyN, (Finset.mem_filter.mp hyS).1⟩
      · have heq := Finset.mem_singleton.mp hy
        subst y
        exact Finset.mem_inter.mpr
          ⟨((hypercube 9).mem_neighborFinset _ _).mpr (flip_adj x 0), hc⟩
  · simp only [hc, ite_false, Finset.union_empty]
    ext y
    constructor
    · intro hy
      obtain ⟨hyN, hyC⟩ := Finset.mem_inter.mp hy
      rcases adjacent_slice_or_cross hx hyC
          (((hypercube 9).mem_neighborFinset _ _).mp hyN) with hys | heq
      · exact Finset.mem_inter.mpr ⟨hyN, hys⟩
      · exact (hc (heq ▸ hyC)).elim
    · intro hy
      obtain ⟨hyN, hyS⟩ := Finset.mem_inter.mp hy
      exact Finset.mem_inter.mpr ⟨hyN, (Finset.mem_filter.mp hyS).1⟩

private theorem induce_degree_card_inter {S : Finset Cube9} {x : Cube9}
    (hx : x ∈ S) :
    ((hypercube 9).induce (S : Set Cube9)).degree ⟨x, hx⟩ =
      ((hypercube 9).neighborFinset x ∩ S).card := by
  have himage : ((((hypercube 9).induce (S : Set Cube9)).neighborFinset
      ⟨x, hx⟩).image (fun y => y.1)) = (hypercube 9).neighborFinset x ∩ S := by
    ext y
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_inter]
    change (∃ a : (S : Set Cube9), (hypercube 9).Adj x a.1 ∧ a.1 = y) ↔ _
    constructor
    · rintro ⟨a, hxa, rfl⟩
      exact ⟨hxa, a.property⟩
    · rintro ⟨hxy, hy⟩
      exact ⟨⟨y, hy⟩, hxy, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  rfl

private theorem coordinate_slice_degree_add_cross {C : Finset Cube9} {b : Bool}
    {x : Cube9} (hx : x ∈ coordinateSlice C b)
    (hr : ((hypercube 9).induce (C : Set Cube9)).IsRegularOfDegree 3) :
    ((hypercube 9).induce (coordinateSlice C b : Set Cube9)).degree ⟨x, hx⟩ +
      (if BalancedCriticalSpectrum.flip x 0 ∈ C then 1 else 0) = 3 := by
  have hcard : ((hypercube 9).neighborFinset x ∩ C).card = 3 := by
    rw [← induce_degree_card_inter (Finset.mem_filter.mp hx).1]
    exact hr.degree_eq _
  rw [neighbor_inter_slice hx] at hcard
  have hdeg := induce_degree_card_inter hx
  by_cases hc : BalancedCriticalSpectrum.flip x 0 ∈ C
  · have hd : Disjoint ((hypercube 9).neighborFinset x ∩ coordinateSlice C b)
        {BalancedCriticalSpectrum.flip x 0} := Finset.disjoint_singleton_right.mpr (fun hm =>
          cross_not_slice hx (Finset.mem_inter.mp hm).2)
    simp only [hc, ite_true] at hcard ⊢
    rwa [Finset.card_union_of_disjoint hd, Finset.card_singleton, ← hdeg] at hcard
  · simp only [hc, ite_false, Finset.union_empty, Nat.add_zero] at hcard ⊢
    rwa [← hdeg] at hcard

private theorem coordinate_slice_degree_cases {C : Finset Cube9} {b : Bool}
    {x : Cube9} (hx : x ∈ coordinateSlice C b)
    (hr : ((hypercube 9).induce (C : Set Cube9)).IsRegularOfDegree 3) :
    ((hypercube 9).induce (coordinateSlice C b : Set Cube9)).degree ⟨x, hx⟩ = 2 ∨
      ((hypercube 9).induce (coordinateSlice C b : Set Cube9)).degree ⟨x, hx⟩ = 3 := by
  have h := coordinate_slice_degree_add_cross hx hr
  split_ifs at h <;> omega

private theorem coordinate_slice_degree_two_iff {C : Finset Cube9} {b : Bool}
    {x : Cube9} (hx : x ∈ coordinateSlice C b)
    (hr : ((hypercube 9).induce (C : Set Cube9)).IsRegularOfDegree 3) :
    ((hypercube 9).induce (coordinateSlice C b : Set Cube9)).degree ⟨x, hx⟩ = 2 ↔
      BalancedCriticalSpectrum.flip x 0 ∈ C := by
  have h := coordinate_slice_degree_add_cross hx hr
  by_cases hc : BalancedCriticalSpectrum.flip x 0 ∈ C
  · simp only [hc, ite_true] at h
    exact ⟨fun _ => hc, fun _ => by omega⟩
  · simp only [hc, ite_false, Nat.add_zero] at h
    exact ⟨fun h2 => by omega, fun hcross => (hc hcross).elim⟩

private theorem crossing_slice_card_eq (C : Finset Cube9) :
    ((coordinateSlice C true).filter (fun x => BalancedCriticalSpectrum.flip x 0 ∈ C)).card =
      ((coordinateSlice C false).filter (fun x => BalancedCriticalSpectrum.flip x 0 ∈ C)).card := by
  apply Finset.card_bij (fun x _ => BalancedCriticalSpectrum.flip x 0)
  · intro x hx
    obtain ⟨hxS, hcross⟩ := Finset.mem_filter.mp hx
    have hx0 := (Finset.mem_filter.mp hxS).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hcross, by simp [BalancedCriticalSpectrum.flip, hx0]⟩,
      by simpa using (Finset.mem_filter.mp hxS).1⟩
  · intro x hx y hy hxy
    have h := congrArg (fun z => BalancedCriticalSpectrum.flip z 0) hxy
    simpa using h
  · intro y hy
    obtain ⟨hyS, hcross⟩ := Finset.mem_filter.mp hy
    have hy0 := (Finset.mem_filter.mp hyS).2
    refine ⟨BalancedCriticalSpectrum.flip y 0, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hcross, by simp [BalancedCriticalSpectrum.flip, hy0]⟩, ?_⟩, by simp⟩
    simpa using (Finset.mem_filter.mp hyS).1

private theorem low_slice_card {C : Finset Cube9} {b : Bool}
    (hr : ((hypercube 9).induce (C : Set Cube9)).IsRegularOfDegree 3) :
    (GirthSliceCounting.degreeTwo
      ((hypercube 9).induce (coordinateSlice C b : Set Cube9)) Finset.univ).card =
      ((coordinateSlice C b).filter (fun x => BalancedCriticalSpectrum.flip x 0 ∈ C)).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    have hx2 := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨x.property,
      (coordinate_slice_degree_two_iff x.property hr).mp hx2⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro y hy
    obtain ⟨hyS, hcross⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨y, hyS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (coordinate_slice_degree_two_iff hyS hr).mpr hcross⟩, rfl⟩

private theorem low_slice_card_eq_q {C : Finset Cube9} {b : Bool}
    (hr : ((hypercube 9).induce (C : Set Cube9)).IsRegularOfDegree 3) :
    (GirthSliceCounting.degreeTwo
      ((hypercube 9).induce (coordinateSlice C b : Set Cube9)) Finset.univ).card =
      directionEdges C 0 := by
  rw [low_slice_card hr]
  cases b with
  | false => simp [coordinateSlice, directionEdges, Finset.filter_filter]
  | true =>
      rw [crossing_slice_card_eq]
      simp [coordinateSlice, directionEdges, Finset.filter_filter]

private theorem coordinate_slice_low_independent {C : Finset Cube9} {b : Bool}
    (hr : ((hypercube 9).induce (C : Set Cube9)).IsRegularOfDegree 3)
    (hb : IsBalanced C) {x y : (coordinateSlice C b : Set Cube9)}
    (hxy : ((hypercube 9).induce (coordinateSlice C b : Set Cube9)).Adj x y)
    (hx : ((hypercube 9).induce (coordinateSlice C b : Set Cube9)).degree x = 2)
    (hy : ((hypercube 9).induce (coordinateSlice C b : Set Cube9)).degree y = 2) :
    False := by
  have hxc := (coordinate_slice_degree_two_iff x.property hr).mp hx
  have hyc := (coordinate_slice_degree_two_iff y.property hr).mp hy
  obtain ⟨i, hi⟩ := adjacent_exists_flip hxy
  have hi0 : i ≠ 0 := by
    intro hi0
    have hy0 : y.val = BalancedCriticalSpectrum.flip x.val 0 := by simpa [hi0] using hi
    exact cross_not_slice x.property (hy0 ▸ y.property)
  apply BalancedCubeGirth.no_selected_square hb hi0
    (Finset.mem_filter.mp x.property).1
    (hi ▸ (Finset.mem_filter.mp y.property).1) hxc
  simpa only [← hi] using hyc

private def paritySide (S : Finset Cube9) (b : Bool) : Finset (S : Set Cube9) :=
  Finset.univ.filter (fun x => cubeParity x.val = b)

private theorem parity_union (S : Finset Cube9) :
    paritySide S false ∪ paritySide S true = Finset.univ := by
  ext x
  cases hx : cubeParity x.val <;> simp [paritySide, hx]

private theorem parity_bipartite (S : Finset Cube9) :
    ((hypercube 9).induce (S : Set Cube9)).IsBipartiteWith
      (paritySide S false : Set (S : Set Cube9))
      (paritySide S true : Set (S : Set Cube9)) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hx0 := (Finset.mem_filter.mp hx).2
    have hx1 := (Finset.mem_filter.mp hy).2
    exact Bool.false_ne_true (hx0.symm.trans hx1)
  · intro x y hxy
    have hne := cubeParity_ne_of_adj hxy
    cases hx : cubeParity x.val <;> cases hy : cubeParity y.val <;>
      simp_all [paritySide]

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

private theorem parts_card (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (S : Finset V) : (degreeTwo G S).card + (degreeThree G S).card = S.card := by
  rw [← Finset.card_union_of_disjoint (degree_parts_disjoint S), degree_parts_union hdeg S]

private theorem sum_degrees_parts (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (S : Finset V) : (∑ v ∈ S, G.degree v) =
      2 * (degreeTwo G S).card + 3 * (degreeThree G S).card := by
  rw [sum_degree_parts hdeg]
  have h2 : (∑ v ∈ degreeTwo G S, G.degree v) = ∑ _v ∈ degreeTwo G S, 2 := by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have h3 : (∑ v ∈ degreeThree G S, G.degree v) = ∑ _v ∈ degreeThree G S, 3 := by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  rw [h2, h3]
  simp [Nat.mul_comm]

private theorem twice_low_le_three_high
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False) :
    2 * (degreeTwo G Finset.univ).card ≤ 3 * (degreeThree G Finset.univ).card := by
  have hleft (v : V) (hv : v ∈ degreeTwo G Finset.univ) :
      (degreeThree G Finset.univ).bipartiteAbove G.Adj v = G.neighborFinset v := by
    ext w
    simp only [Finset.mem_bipartiteAbove, degreeThree, Finset.mem_filter,
      Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · exact And.right
    · intro hvw
      have hw3 : G.degree w = 3 := by
        rcases hdeg w with hw2 | hw3
        · exact (hlow hvw (Finset.mem_filter.mp hv).2 hw2).elim
        · exact hw3
      exact ⟨hw3, hvw⟩
  have hright (w : V) (hw : w ∈ degreeThree G Finset.univ) :
      ((degreeTwo G Finset.univ).bipartiteBelow G.Adj w).card ≤ 3 := by
    have hs : (degreeTwo G Finset.univ).bipartiteBelow G.Adj w ⊆
        G.neighborFinset w := by
      intro v hv
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_bipartiteBelow.mp hv).2.symm
    calc
      _ ≤ (G.neighborFinset w).card := Finset.card_le_card hs
      _ = 3 := (Finset.mem_filter.mp hw).2
  have h := Finset.card_mul_le_card_mul (r := G.Adj)
    (s := degreeTwo G Finset.univ) (t := degreeThree G Finset.univ)
    (m := 2) (n := 3) (fun v hv => by
      rw [hleft v hv, SimpleGraph.card_neighborFinset_eq_degree,
        (Finset.mem_filter.mp hv).2]) hright
  simpa [Nat.mul_comm] using h

end Counting

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
