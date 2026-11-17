/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceIncidence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Forced leaf incidences in the nineteen-vertex equality tree. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceTree

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

open private treeParent treeChildren from
  D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceTree

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


end D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSlice
