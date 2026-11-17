/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceMatching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Cubical matching-middle obstruction for the nineteen-vertex equality tree. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceIncidence

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

open private leafRow leafCol colParent leafOrder fork_leaf_incidence
  fork_leaf_choices from
  D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceIncidence

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


end D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSlice
