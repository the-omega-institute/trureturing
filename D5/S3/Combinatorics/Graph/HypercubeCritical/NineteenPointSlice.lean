/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSlice
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Actual balanced cubic Q9 slices of size at most nineteen reconstruct Gray support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceMatching

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

open private eleven_low_nineteen_impossible high_fork_exists treeParent treeChildren fork_tree_vertices
  high_edge_neighbor_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceTree

open private labelled_matching_obstruction fork_matching_configuration from
  D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceMatching

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

end D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSlice
