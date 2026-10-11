/- GID: D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DominatingSetAverageBoundStem
   mirror-E: none(waiver:finite-stem-counting)
   anchors: []
   utility: none
   digest: Leaf-stem substitutions and exact local critical-vertex counts. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.DominatingSetAverageBoundStem

open Finset
open D5.S3.Combinatorics.Graph.DominatingSetAverage
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- A stem together with all of its leaf neighbours. -/
noncomputable def stemBlock (s : V) : Finset V := insert s (leafNeighbors G s)

/-- Replace all leaf neighbours by the stem and a chosen subset of its leaves. -/
noncomputable def stemSwap (s : V) (S T : Finset V) : Finset V :=
  insert s (S \ leafNeighbors G s) ∪ T

/-- A leaf neighbour's only neighbour is its stem. -/
theorem leaf_neighbor_only {s x y : V} (hx : x ∈ leafNeighbors G s)
    (hxy : G.Adj x y) : y = s :=
  leaf_adj_unique (mem_leafNeighbors.mp hx).2
    (G.adj_symm (mem_leafNeighbors.mp hx).1) hxy

/-- A stem cannot be one of its own leaf neighbours. -/
theorem stem_not_leafNeighbor (s : V) : s ∉ leafNeighbors G s := by
  simp only [mem_leafNeighbors, G.loopless.irrefl, false_and, not_false_eq_true]

/-- Omitting a stem forces all of its leaf neighbours into a dominating set. -/
theorem leafNeighbors_subset_of_stem_notMem {s : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hs : s ∉ S) : leafNeighbors G s ⊆ S := by
  intro x hx
  rcases hS x with h | ⟨y, hy, hxy⟩
  · exact h
  · exact False.elim (hs (leaf_neighbor_only G hx hxy ▸ hy))

/-- Selecting the stem makes its selected leaves removable. -/
theorem leaf_not_critical_of_stem_mem {s x : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hs : s ∈ S)
    (hx : x ∈ leafNeighbors G s) : x ∉ criticalVertices G S := by
  classical
  have hxs : x ≠ s := by
    intro h
    exact stem_not_leafNeighbor G s (h ▸ hx)
  have hd : G.IsDominating (S.erase x : Set V) := by
    intro y
    by_cases hyx : y = x
    · subst y
      exact Or.inr ⟨s, mem_erase.mpr ⟨hxs.symm, hs⟩,
        G.adj_symm (mem_leafNeighbors.mp hx).1⟩
    rcases hS y with hy | ⟨z, hz, hyz⟩
    · exact Or.inl (mem_erase.mpr ⟨hyx, hy⟩)
    · by_cases hzx : z = x
      · subst z
        have hys : y = s := leaf_neighbor_only G hx (G.adj_symm hyz)
        subst y
        exact Or.inl (mem_erase.mpr ⟨hxs.symm, hs⟩)
      · exact Or.inr ⟨z, mem_erase.mpr ⟨hzx, hz⟩, hyz⟩
  intro hc
  exact (mem_filter.mp hc).2 hd

/-- An omitted leaf witnesses criticality of its selected stem. -/
theorem stem_critical_of_leaf_notMem {s x : V} {S : Finset V}
    (hs : s ∈ S) (hx : x ∈ leafNeighbors G s) (hxS : x ∉ S) :
    s ∈ criticalVertices G S := by
  classical
  refine mem_filter.mpr ⟨hs, ?_⟩
  intro hd
  rcases hd x with h | ⟨y, hy, hxy⟩
  · exact hxS (mem_erase.mp h).2
  · have hys := leaf_neighbor_only G hx hxy
    exact (mem_erase.mp hy).1 hys

/-- If the stem is absent, each selected leaf is critical. -/
theorem leaf_critical_of_stem_notMem {s x : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hs : s ∉ S)
    (hx : x ∈ leafNeighbors G s) : x ∈ criticalVertices G S := by
  classical
  have hxS := leafNeighbors_subset_of_stem_notMem G hS hs hx
  refine mem_filter.mpr ⟨hxS, ?_⟩
  intro hd
  rcases hd x with h | ⟨y, hy, hxy⟩
  · exact (mem_erase.mp h).1 rfl
  · exact hs (mem_erase.mp (leaf_neighbor_only G hx hxy ▸ hy)).2

/-- Proper leaf choices together with the stem leave exactly the stem critical in its block. -/
theorem critical_inter_block_stem_mem {s : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hs : s ∈ S)
    (hL : ¬ leafNeighbors G s ⊆ S) :
    criticalVertices G S ∩ stemBlock G s = {s} := by
  classical
  obtain ⟨x, hx, hxS⟩ := not_subset.mp hL
  have hsc := stem_critical_of_leaf_notMem G hs hx hxS
  ext y
  simp only [mem_inter, stemBlock, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hy, hys | hyL⟩
    · exact hys
    · exact False.elim (leaf_not_critical_of_stem_mem G hS hs hyL hy)
  · rintro rfl
    exact ⟨hsc, Or.inl rfl⟩

/-- Without its stem, the critical vertices of a stem block are precisely its leaves. -/
theorem critical_inter_block_stem_notMem {s : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hs : s ∉ S) :
    criticalVertices G S ∩ stemBlock G s = leafNeighbors G s := by
  classical
  ext y
  simp only [mem_inter, stemBlock, mem_insert]
  constructor
  · rintro ⟨hy, hys | hyL⟩
    · subst y
      exact False.elim (hs (mem_filter.mp hy).1)
    · exact hyL
  · intro hyL
    exact ⟨leaf_critical_of_stem_notMem G hS hs hyL, Or.inr hyL⟩

/-- A dominating set omitting a stem remains dominating after replacement by the stem. -/
theorem stemSwap_dominating {s : V} {S T : Finset V}
    (hS : G.IsDominating (S : Set V)) :
    G.IsDominating (stemSwap G s S T : Set V) := by
  intro x
  by_cases hxL : x ∈ leafNeighbors G s
  · exact Or.inr ⟨s, mem_union_left _ (mem_insert_self _ _),
      G.adj_symm (mem_leafNeighbors.mp hxL).1⟩
  rcases hS x with hx | ⟨y, hy, hxy⟩
  · exact Or.inl (mem_union_left _ (mem_insert_of_mem (mem_sdiff.mpr ⟨hx, hxL⟩)))
  · by_cases hyL : y ∈ leafNeighbors G s
    · have hxs : x = s := leaf_neighbor_only G hyL (G.adj_symm hxy)
      subst x
      exact Or.inl (mem_union_left _ (mem_insert_self _ _))
    · exact Or.inr ⟨y,
        mem_union_left _ (mem_insert_of_mem (mem_sdiff.mpr ⟨hy, hyL⟩)), hxy⟩

/-- The inserted leaf subset is recovered by intersection with the leaf block. -/
theorem stemSwap_inter_leaves (s : V) (S T : Finset V)
    (hT : T ⊆ leafNeighbors G s) : stemSwap G s S T ∩ leafNeighbors G s = T := by
  classical
  ext x
  simp only [stemSwap, mem_inter, mem_union, mem_insert, mem_sdiff]
  constructor
  · rintro ⟨(hxs | ⟨hxS, hxL⟩) | hxT, hxL'⟩
    · exact False.elim (stem_not_leafNeighbor G s (hxs ▸ hxL'))
    · exact False.elim (hxL hxL')
    · exact hxT
  · intro hxT
    exact ⟨Or.inr hxT, hT hxT⟩

/-- Removing the block after substitution recovers the original outside choice. -/
theorem stemSwap_sdiff_block {s : V} {S T : Finset V}
    (hs : s ∉ S) (hT : T ⊆ leafNeighbors G s) :
    stemSwap G s S T \ stemBlock G s = S \ leafNeighbors G s := by
  classical
  ext x
  simp only [stemSwap, stemBlock, mem_sdiff, mem_union, mem_insert, not_or]
  constructor
  · rintro ⟨(hxs | hx) | hxT, hxns, hxL⟩
    · exact False.elim (hxns hxs)
    · exact hx
    · exact False.elim (hxL (hT hxT))
  · rintro ⟨hxS, hxL⟩
    exact ⟨Or.inl (Or.inr ⟨hxS, hxL⟩), (fun h => hs (h ▸ hxS)), hxL⟩

/-- Stem substitution is injective in the omitted-stem set and proper leaf choice. -/
theorem stemSwap_injective {s : V} {S R T Q : Finset V}
    (hS : G.IsDominating (S : Set V)) (hR : G.IsDominating (R : Set V))
    (hsS : s ∉ S) (hsR : s ∉ R)
    (hT : T ⊆ leafNeighbors G s) (hQ : Q ⊆ leafNeighbors G s)
    (heq : stemSwap G s S T = stemSwap G s R Q) : S = R ∧ T = Q := by
  have hTQ : T = Q := by
    rw [← stemSwap_inter_leaves G s S T hT, heq, stemSwap_inter_leaves G s R Q hQ]
  have hout : S \ leafNeighbors G s = R \ leafNeighbors G s := by
    rw [← stemSwap_sdiff_block G hsS hT, heq, stemSwap_sdiff_block G hsR hQ]
  have hLS := leafNeighbors_subset_of_stem_notMem G hS hsS
  have hLR := leafNeighbors_subset_of_stem_notMem G hR hsR
  constructor
  · rw [← sdiff_union_of_subset hLS, hout, sdiff_union_of_subset hLR]
  · exact hTQ

/-- The stem is the sole omitted block vertex when it is not selected. -/
theorem block_sdiff_stem_notMem {s : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hs : s ∉ S) :
    stemBlock G s \ S = {s} := by
  classical
  have hL := leafNeighbors_subset_of_stem_notMem G hS hs
  ext x
  simp only [stemBlock, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hxs | hxL, hxS⟩
    · exact hxs
    · exact False.elim (hxS (hL hxL))
  · rintro rfl
    exact ⟨Or.inl rfl, hs⟩

/-- Selecting a stem leaves exactly the unselected leaves omitted from its block. -/
theorem block_sdiff_stem_mem {s : V} {S : Finset V} (hs : s ∈ S) :
    stemBlock G s \ S = leafNeighbors G s \ S := by
  classical
  ext x
  simp only [stemBlock, mem_sdiff, mem_insert]
  constructor
  · rintro ⟨hxs | hxL, hxS⟩
    · exact False.elim (hxS (hxs ▸ hs))
    · exact ⟨hxL, hxS⟩
  · exact fun ⟨hxL, hxS⟩ => ⟨Or.inr hxL, hxS⟩

/-- A proper leaf choice in a substituted set leaves the stem block active. -/
theorem stemSwap_block_not_subset {s : V} {S T : Finset V}
    (hT : T ⊆ leafNeighbors G s) (hproper : T ≠ leafNeighbors G s) :
    ¬ stemBlock G s ⊆ stemSwap G s S T := by
  classical
  intro hfull
  apply hproper
  apply subset_antisymm hT
  intro x hx
  have hxm : x ∈ stemSwap G s S T ∩ leafNeighbors G s :=
    mem_inter.mpr ⟨hfull (mem_insert_of_mem hx), hx⟩
  rwa [stemSwap_inter_leaves G s S T hT] at hxm

/-- The difference between omitted and critical vertices in a stem block. -/
noncomputable def stemGap (s : V) (S : Finset V) : ℤ :=
  ((stemBlock G s \ S).card : ℤ) - (criticalVertices G S ∩ stemBlock G s).card

/-- In an active selected-stem block, the critical count is bounded by the omitted count. -/
theorem stemGap_nonneg_stem_mem {s : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hs : s ∈ S)
    (hactive : ¬ stemBlock G s ⊆ S) : 0 ≤ stemGap G s S := by
  classical
  have hL : ¬ leafNeighbors G s ⊆ S := by
    intro hL
    apply hactive
    exact insert_subset_iff.mpr ⟨hs, hL⟩
  have hnon : (leafNeighbors G s \ S).Nonempty := by
    obtain ⟨x, hxL, hxS⟩ := not_subset.mp hL
    exact ⟨x, mem_sdiff.mpr ⟨hxL, hxS⟩⟩
  rw [stemGap, critical_inter_block_stem_mem G hS hs hL,
    block_sdiff_stem_mem G hs, card_singleton]
  exact sub_nonneg.mpr (by exact_mod_cast card_pos.mpr hnon)

/-- An omitted-stem choice and its empty-leaf replacement have opposite gaps. -/
theorem stemGap_empty_swap {s : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hs : s ∉ S)
    (hL : (leafNeighbors G s).Nonempty) :
    stemGap G s (stemSwap G s S ∅) = - stemGap G s S := by
  classical
  have hTL : (∅ : Finset V) ⊆ leafNeighbors G s := empty_subset _
  have hne : (∅ : Finset V) ≠ leafNeighbors G s := by
    intro h; exact hL.ne_empty h.symm
  have hs' : s ∈ stemSwap G s S ∅ := mem_union_left _ (mem_insert_self _ _)
  have hLn : ¬ leafNeighbors G s ⊆ stemSwap G s S ∅ := by
    intro hfull
    exact stemSwap_block_not_subset G hTL hne (insert_subset_iff.mpr ⟨hs', hfull⟩)
  have hdis : Disjoint (leafNeighbors G s) (stemSwap G s S ∅) := by
    rw [disjoint_iff_inter_eq_empty, inter_comm,
      stemSwap_inter_leaves G s S ∅ hTL]
  rw [stemGap, stemGap, block_sdiff_stem_notMem G hS hs,
    critical_inter_block_stem_notMem G hS hs,
    critical_inter_block_stem_mem G (stemSwap_dominating G hS) hs' hLn,
    block_sdiff_stem_mem G hs', sdiff_eq_left.mpr hdis,
    card_singleton]
  ring

/-- Stem-block counting in any active family closed under the empty-leaf replacement. -/
theorem active_stem_family_bound
    (s : V) (F : Finset (Finset V))
    (hL : (leafNeighbors G s).Nonempty)
    (hdom : ∀ S ∈ F, G.IsDominating (S : Set V))
    (hactive : ∀ S ∈ F, ¬ stemBlock G s ⊆ S)
    (hclosed : ∀ S ∈ F, s ∉ S → stemSwap G s S ∅ ∈ F) :
    (∑ S ∈ F, (criticalVertices G S ∩ stemBlock G s).card) ≤
    ∑ S ∈ F, (stemBlock G s \ S).card := by
  classical
  let O := F.filter fun S => s ∉ S
  let P := F.filter fun S => s ∈ S
  let f := fun S => stemSwap G s S ∅
  let I := O.image f
  have hOP : Disjoint O P := by
    rw [disjoint_left]
    intro S hSO hSP
    exact (mem_filter.mp hSO).2 (mem_filter.mp hSP).2
  have hF : O ∪ P = F := by
    ext S; simp [O, P]; tauto
  have hfmem (S : Finset V) (hS : S ∈ O) : f S ∈ P := by
    rcases mem_filter.mp hS with ⟨hSF, hs⟩
    exact mem_filter.mpr ⟨hclosed S hSF hs, mem_union_left _ (mem_insert_self _ _)⟩
  have hIP : I ⊆ P := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hT
    exact hfmem S hS
  have hinj : Set.InjOn f (O : Set (Finset V)) := by
    intro S hS R hR heq
    rcases mem_filter.mp hS with ⟨hSF, hsS⟩
    rcases mem_filter.mp hR with ⟨hRF, hsR⟩
    exact (stemSwap_injective G (hdom S hSF) (hdom R hRF)
      hsS hsR (empty_subset _) (empty_subset _) heq).1
  have hsumI : ∑ S ∈ I, stemGap G s S = - ∑ S ∈ O, stemGap G s S := by
    rw [show I = O.image f from rfl, sum_image hinj, ← sum_neg_distrib]
    apply sum_congr rfl
    intro S hS
    rcases mem_filter.mp hS with ⟨hSF, hs⟩
    exact stemGap_empty_swap G (hdom S hSF) hs hL
  have hrem : 0 ≤ ∑ S ∈ P \ I, stemGap G s S := by
    apply sum_nonneg
    intro S hS
    have hSP := (mem_sdiff.mp hS).1
    rcases mem_filter.mp hSP with ⟨hSF, hs⟩
    exact stemGap_nonneg_stem_mem G (hdom S hSF) hs (hactive S hSF)
  have hsumP : ∑ S ∈ P, stemGap G s S =
      (∑ S ∈ P \ I, stemGap G s S) + ∑ S ∈ I, stemGap G s S := by
    exact (sum_sdiff hIP).symm
  have hgap : 0 ≤ ∑ S ∈ F, stemGap G s S := by
    rw [← hF, sum_union hOP, hsumP, hsumI]
    linarith
  simp only [stemGap, sum_sub_distrib] at hgap
  exact_mod_cast sub_nonneg.mp hgap

/-- Adjacent leaves constitute the same two-vertex block from either endpoint. -/
theorem stemBlock_eq_of_leaf_mem {s t : V}
    (hs : s ∈ leafNeighbors G t) (hLs : (leafNeighbors G s).Nonempty) :
    stemBlock G s = stemBlock G t := by
  classical
  obtain ⟨u, hu⟩ := hLs
  have hut : u = t := leaf_adj_unique (mem_leafNeighbors.mp hs).2
    (G.adj_symm (mem_leafNeighbors.mp hs).1) (mem_leafNeighbors.mp hu).1
  have ht : Leaf G t := hut ▸ (mem_leafNeighbors.mp hu).2
  have hst : G.Adj s t := G.adj_symm (mem_leafNeighbors.mp hs).1
  have hLsEq : leafNeighbors G s = {t} := by
    ext x
    simp only [mem_leafNeighbors, mem_singleton]
    constructor
    · intro hx
      exact leaf_adj_unique (mem_leafNeighbors.mp hs).2 hst hx.1
    · rintro rfl
      exact ⟨hst, ht⟩
  have hLtEq : leafNeighbors G t = {s} := by
    ext x
    simp only [mem_leafNeighbors, mem_singleton]
    constructor
    · intro hx
      exact leaf_adj_unique ht (mem_leafNeighbors.mp hs).1 hx.1
    · rintro rfl
      exact mem_leafNeighbors.mp hs
  simp only [stemBlock, hLsEq, hLtEq]
  exact pair_comm s t

/-- Stem blocks are disjoint except for the identical blocks of a two-leaf component. -/
theorem stemBlocks_disjoint_or_eq {s t : V}
    (hLs : (leafNeighbors G s).Nonempty) (hLt : (leafNeighbors G t).Nonempty) :
    Disjoint (stemBlock G s) (stemBlock G t) ∨ stemBlock G s = stemBlock G t := by
  classical
  by_cases hdis : Disjoint (stemBlock G s) (stemBlock G t)
  · exact Or.inl hdis
  right
  rw [disjoint_left] at hdis
  push Not at hdis
  obtain ⟨x, hxS, hxT⟩ := hdis
  rcases mem_insert.mp hxS with hxs | hxL
  · subst x
    rcases mem_insert.mp hxT with hst | hsL
    · subst s
      rfl
    · exact stemBlock_eq_of_leaf_mem G hsL hLs
  · rcases mem_insert.mp hxT with hxt | hxL'
    · subst x
      exact (stemBlock_eq_of_leaf_mem G hxL hLt).symm
    · have hst : s = t := leaf_neighbor_only G hxL' (G.adj_symm (mem_leafNeighbors.mp hxL).1)
      subst s
      rfl

/-- The distinct stem blocks; the two descriptions of a two-leaf component occur only once. -/
noncomputable def stemBlocks : Finset (Finset V) := by
  classical
  exact (univ.filter fun s => (leafNeighbors G s).Nonempty).image (stemBlock G)

/-- Every stem block has a stem witness with a nonempty leaf-neighbour set. -/
theorem mem_stemBlocks {B : Finset V} : B ∈ stemBlocks G ↔
    ∃ s, (leafNeighbors G s).Nonempty ∧ stemBlock G s = B := by
  classical
  simp [stemBlocks]

/-- Distinct stem blocks are disjoint. -/
theorem stemBlocks_pairwiseDisjoint :
    (stemBlocks G : Set (Finset V)).Pairwise Disjoint := by
  intro B hB C hC hne
  obtain ⟨s, hs, rfl⟩ := (mem_stemBlocks G).mp hB
  obtain ⟨t, ht, rfl⟩ := (mem_stemBlocks G).mp hC
  rcases stemBlocks_disjoint_or_eq G hs ht with hdis | heq
  · exact hdis
  · exact False.elim (hne heq)

/-- Every stem belongs to one of the distinct stem blocks. -/
theorem vertex_mem_stemBlocks_of_stem {s : V} (hs : (leafNeighbors G s).Nonempty) :
    s ∈ (stemBlocks G).biUnion id := by
  classical
  refine mem_biUnion.mpr ⟨stemBlock G s, (mem_stemBlocks G).mpr ⟨s, hs, rfl⟩, ?_⟩
  exact mem_insert_self _ _

/-- Every leaf belongs to a stem block. -/
theorem vertex_mem_stemBlocks_of_leaf {x : V} (hx : Leaf G x) :
    x ∈ (stemBlocks G).biUnion id := by
  classical
  obtain ⟨s, hxs, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hx
  have hxL : x ∈ leafNeighbors G s := mem_leafNeighbors.mpr ⟨hxs.symm, hx⟩
  refine mem_biUnion.mpr ⟨stemBlock G s,
    (mem_stemBlocks G).mpr ⟨s, ⟨x, hxL⟩, rfl⟩, ?_⟩
  exact mem_insert_of_mem hxL

/-- The dominating sets in which a specified stem block is not wholly selected. -/
noncomputable def activeStemFamily (s : V) : Finset (Finset V) := by
  classical
  exact (domSets G).filter fun S => ¬ stemBlock G s ⊆ S

/-- Empty-leaf substitution stays within the active family. -/
theorem empty_stemSwap_mem_active {s : V} {S : Finset V}
    (hL : (leafNeighbors G s).Nonempty) (hS : S ∈ activeStemFamily G s) :
    stemSwap G s S ∅ ∈ activeStemFamily G s := by
  classical
  refine mem_filter.mpr ⟨mem_domSets.mpr (stemSwap_dominating G (mem_domSets.mp
    (mem_filter.mp hS).1)), ?_⟩
  apply stemSwap_block_not_subset G (empty_subset _)
  exact fun h => hL.ne_empty h.symm

/-- A stem block contributes no more critical than omitted vertices over its active sets. -/
theorem activeStemFamily_bound (s : V) (hLs : (leafNeighbors G s).Nonempty) :
    (∑ S ∈ activeStemFamily G s, (criticalVertices G S ∩ stemBlock G s).card) ≤
    ∑ S ∈ activeStemFamily G s, (stemBlock G s \ S).card := by
  classical
  apply active_stem_family_bound G s (activeStemFamily G s) hLs
  · intro S hS
    exact mem_domSets.mp (mem_filter.mp hS).1
  · intro S hS
    exact (mem_filter.mp hS).2
  · intro S hS _
    exact empty_stemSwap_mem_active G hLs hS

/-- Proper leaf substitution omits exactly the leaves outside the chosen subset. -/
theorem stemSwap_block_sdiff (s : V) (S T : Finset V)
    (hT : T ⊆ leafNeighbors G s) :
    stemBlock G s \ stemSwap G s S T = leafNeighbors G s \ T := by
  classical
  have hs : s ∈ stemSwap G s S T := mem_union_left _ (mem_insert_self _ _)
  rw [block_sdiff_stem_mem G hs]
  ext x
  simp only [mem_sdiff]
  constructor
  · rintro ⟨hxL, hxF⟩
    exact ⟨hxL, fun hxT => hxF (mem_union_right _ hxT)⟩
  · rintro ⟨hxL, hxT⟩
    refine ⟨hxL, ?_⟩
    intro hxF
    have hxI := mem_inter.mpr ⟨hxF, hxL⟩
    rw [stemSwap_inter_leaves G s S T hT] at hxI
    exact hxT hxI

/-- A positive selected-stem gap makes the active-family bound strict. -/
theorem active_stem_family_strict
    (s : V) (F : Finset (Finset V))
    (hL : (leafNeighbors G s).Nonempty)
    (hdom : ∀ S ∈ F, G.IsDominating (S : Set V))
    (hactive : ∀ S ∈ F, ¬ stemBlock G s ⊆ S)
    (hclosed : ∀ S ∈ F, s ∉ S → stemSwap G s S ∅ ∈ F)
    (hpos : ∃ R ∈ F, s ∈ R ∧ (R ∩ leafNeighbors G s).Nonempty ∧
      0 < stemGap G s R) :
    (∑ S ∈ F, (criticalVertices G S ∩ stemBlock G s).card) <
    ∑ S ∈ F, (stemBlock G s \ S).card := by
  classical
  let O := F.filter fun S => s ∉ S
  let P := F.filter fun S => s ∈ S
  let f := fun S => stemSwap G s S ∅
  let I := O.image f
  have hOP : Disjoint O P := by
    rw [disjoint_left]
    intro S hSO hSP
    exact (mem_filter.mp hSO).2 (mem_filter.mp hSP).2
  have hF : O ∪ P = F := by
    ext S; simp [O, P]; tauto
  have hfmem (S : Finset V) (hS : S ∈ O) : f S ∈ P := by
    rcases mem_filter.mp hS with ⟨hSF, hs⟩
    exact mem_filter.mpr ⟨hclosed S hSF hs, mem_union_left _ (mem_insert_self _ _)⟩
  have hIP : I ⊆ P := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hT
    exact hfmem S hS
  have hinj : Set.InjOn f (O : Set (Finset V)) := by
    intro S hS R hR heq
    rcases mem_filter.mp hS with ⟨hSF, hsS⟩
    rcases mem_filter.mp hR with ⟨hRF, hsR⟩
    exact (stemSwap_injective G (hdom S hSF) (hdom R hRF)
      hsS hsR (empty_subset _) (empty_subset _) heq).1
  have hsumI : ∑ S ∈ I, stemGap G s S = - ∑ S ∈ O, stemGap G s S := by
    rw [show I = O.image f from rfl, sum_image hinj, ← sum_neg_distrib]
    apply sum_congr rfl
    intro S hS
    rcases mem_filter.mp hS with ⟨hSF, hs⟩
    exact stemGap_empty_swap G (hdom S hSF) hs hL
  have hrem : 0 < ∑ S ∈ P \ I, stemGap G s S := by
    apply sum_pos'
    · intro S hS
      rcases mem_filter.mp (mem_sdiff.mp hS).1 with ⟨hSF, hs⟩
      exact stemGap_nonneg_stem_mem G (hdom S hSF) hs (hactive S hSF)
    · obtain ⟨R, hRF, hsR, hRL, hgap⟩ := hpos
      refine ⟨R, mem_sdiff.mpr ⟨mem_filter.mpr ⟨hRF, hsR⟩, ?_⟩, hgap⟩
      intro hRI
      obtain ⟨S, _, hSR⟩ := mem_image.mp hRI
      have hemp : R ∩ leafNeighbors G s = ∅ := by
        rw [← hSR]
        exact stemSwap_inter_leaves G s S ∅ (empty_subset _)
      exact hRL.ne_empty hemp
  have hsumP : ∑ S ∈ P, stemGap G s S =
      (∑ S ∈ P \ I, stemGap G s S) + ∑ S ∈ I, stemGap G s S :=
    (sum_sdiff hIP).symm
  have hgap : 0 < ∑ S ∈ F, stemGap G s S := by
    rw [← hF, sum_union hOP, hsumP, hsumI]
    linarith
  simp only [stemGap, sum_sub_distrib] at hgap
  exact_mod_cast sub_pos.mp hgap

/-- The local stem contribution is strict once there are at least three leaf neighbours. -/
theorem activeStemFamily_strict (s : V) (hk : 3 ≤ leafCount G s) :
    (∑ S ∈ activeStemFamily G s, (criticalVertices G S ∩ stemBlock G s).card) <
    ∑ S ∈ activeStemFamily G s, (stemBlock G s \ S).card := by
  classical
  have hk' : 3 ≤ (leafNeighbors G s).card := hk
  have hL : (leafNeighbors G s).Nonempty := card_pos.mp (by omega)
  obtain ⟨x, hxL⟩ := hL
  have hL : (leafNeighbors G s).Nonempty := ⟨x, hxL⟩
  have hxs : x ≠ s := by
    intro h; exact stem_not_leafNeighbor G s (h ▸ hxL)
  let S : Finset V := univ.erase s
  have hsS : s ∉ S := by simp [S]
  have hdomS : G.IsDominating (S : Set V) := by
    intro y
    by_cases hys : y = s
    · subst y
      exact Or.inr ⟨x, by simp [S, hxs], (mem_leafNeighbors.mp hxL).1⟩
    · exact Or.inl (by simp [S, hys])
  have hT : ({x} : Finset V) ⊆ leafNeighbors G s := singleton_subset_iff.mpr hxL
  have hproper : ({x} : Finset V) ≠ leafNeighbors G s := by
    intro h
    have : (leafNeighbors G s).card = 1 := by rw [← h]; exact card_singleton x
    omega
  let R := stemSwap G s S {x}
  have hdomR : G.IsDominating (R : Set V) := stemSwap_dominating G hdomS
  have hsR : s ∈ R := mem_union_left _ (mem_insert_self _ _)
  have hactiveR : ¬ stemBlock G s ⊆ R := stemSwap_block_not_subset G hT hproper
  have hLn : ¬ leafNeighbors G s ⊆ R := by
    intro h; exact hactiveR (insert_subset_iff.mpr ⟨hsR, h⟩)
  have hgapR : 0 < stemGap G s R := by
    rw [stemGap, critical_inter_block_stem_mem G hdomR hsR hLn,
      stemSwap_block_sdiff G s S {x} hT, card_sdiff_of_subset hT, card_singleton]
    have : 1 < (leafNeighbors G s).card - 1 := by omega
    exact sub_pos.mpr (by exact_mod_cast this)
  apply active_stem_family_strict G s (activeStemFamily G s) hL
  · intro T hT
    exact mem_domSets.mp (mem_filter.mp hT).1
  · intro T hT
    exact (mem_filter.mp hT).2
  · intro T hT _
    exact empty_stemSwap_mem_active G hL hT
  · refine ⟨R, mem_filter.mpr ⟨mem_domSets.mpr hdomR, hactiveR⟩, hsR, ?_, hgapR⟩
    exact ⟨x, mem_inter.mpr ⟨mem_union_right _ (mem_singleton_self x), hxL⟩⟩

/-- Replacing a non-leaf stem by all its leaves preserves domination in a star-like graph. -/
theorem stemUndo_dominating_starLike {s : V} {R : Finset V}
    (hstar : StarLike G) (hL : (leafNeighbors G s).Nonempty) (hsLeaf : ¬ Leaf G s)
    (hR : G.IsDominating (R : Set V)) :
    G.IsDominating ((R.erase s ∪ leafNeighbors G s : Finset V) : Set V) := by
  change ∀ x, x ∈ (R.erase s ∪ leafNeighbors G s : Finset V) ∨
    ∃ y ∈ (R.erase s ∪ leafNeighbors G s : Finset V), G.Adj x y
  classical
  intro x
  by_cases hxL : x ∈ leafNeighbors G s
  · exact Or.inl (mem_union_right _ hxL)
  by_cases hxs : x = s
  · subst x
    obtain ⟨u, hu⟩ := hL
    exact Or.inr ⟨u, mem_union_right _ hu, (mem_leafNeighbors.mp hu).1⟩
  rcases hR x with hx | ⟨y, hy, hxy⟩
  · exact Or.inl (mem_union_left _ (mem_erase.mpr ⟨hxs, hx⟩))
  · by_cases hys : y = s
    · subst y
      have hxLeaf : ¬ Leaf G x := by
        intro hleaf
        exact hxL (mem_leafNeighbors.mpr ⟨hxy.symm, hleaf⟩)
      have hxcount : leafCount G x = 1 ∨ leafCount G x = 2 :=
        (hstar x).resolve_left hxLeaf
      have hxnon : (leafNeighbors G x).Nonempty := by
        apply card_pos.mp
        change 0 < leafCount G x
        rcases hxcount with h | h <;> omega
      obtain ⟨u, hu⟩ := hxnon
      have hus : u ≠ s := by
        intro h; exact hsLeaf (h ▸ (mem_leafNeighbors.mp hu).2)
      rcases (leaf_dominated_iff (mem_leafNeighbors.mp hu).2
          (G.adj_symm (mem_leafNeighbors.mp hu).1) R).mp (hR u) with huR | hxR
      · exact Or.inr ⟨u, mem_union_left _ (mem_erase.mpr ⟨hus, huR⟩),
          (mem_leafNeighbors.mp hu).1⟩
      · exact Or.inl (mem_union_left _ (mem_erase.mpr ⟨hxs, hxR⟩))
    · exact Or.inr ⟨y, mem_union_left _ (mem_erase.mpr ⟨hys, hy⟩), hxy⟩

/-- A leaf can have at most one leaf neighbour. -/
theorem leafCount_le_one_of_leaf {s : V} (hs : Leaf G s) : leafCount G s ≤ 1 := by
  classical
  change (leafNeighbors G s).card ≤ 1
  apply card_le_one.mpr
  intro x hx y hy
  exact leaf_adj_unique hs (mem_leafNeighbors.mp hy).1 (mem_leafNeighbors.mp hx).1

/-- Every empty-leaf selected-stem set has an omitted-stem predecessor in a star-like graph. -/
theorem emptyLeaf_predecessor_starLike {s : V} {R : Finset V}
    (hstar : StarLike G) (hk : leafCount G s = 2)
    (hR : G.IsDominating (R : Set V)) (hsR : s ∈ R)
    (hinter : R ∩ leafNeighbors G s = ∅) :
    ∃ S ∈ activeStemFamily G s, s ∉ S ∧ stemSwap G s S ∅ = R := by
  classical
  have hL : (leafNeighbors G s).Nonempty := card_pos.mp (by change 0 < leafCount G s; omega)
  have hsLeaf : ¬ Leaf G s := by
    intro h
    have := leafCount_le_one_of_leaf G h
    omega
  let S := R.erase s ∪ leafNeighbors G s
  have hsS : s ∉ S := by simp [S, stem_not_leafNeighbor G s]
  have hdomS : G.IsDominating (S : Set V) := stemUndo_dominating_starLike G hstar hL hsLeaf hR
  have hS : S ∈ activeStemFamily G s := by
    refine mem_filter.mpr ⟨mem_domSets.mpr hdomS, ?_⟩
    exact fun h => hsS (h (mem_insert_self _ _))
  refine ⟨S, hS, hsS, ?_⟩
  have hdis : Disjoint R (leafNeighbors G s) := disjoint_iff_inter_eq_empty.mpr hinter
  ext x
  simp only [stemSwap, S, mem_union, mem_insert, mem_sdiff, mem_erase, notMem_empty,
    or_false]
  constructor
  · rintro (hxs | ⟨⟨hxs, hxR⟩ | hxL, hxnotL⟩)
    · exact hxs ▸ hsR
    · exact hxR
    · exact False.elim (hxnotL hxL)
  · intro hxR
    by_cases hxs : x = s
    · exact Or.inl hxs
    · exact Or.inr ⟨Or.inl ⟨hxs, hxR⟩, fun hxL => disjoint_left.mp hdis hxR hxL⟩

/-- Exact balance when every unpaired selected-stem set has zero gap. -/
theorem active_stem_family_eq
    (s : V) (F : Finset (Finset V))
    (hL : (leafNeighbors G s).Nonempty)
    (hdom : ∀ S ∈ F, G.IsDominating (S : Set V))
    (hclosed : ∀ S ∈ F, s ∉ S → stemSwap G s S ∅ ∈ F)
    (hzero : ∀ R ∈ F, s ∈ R →
      (∀ S ∈ F, s ∉ S → stemSwap G s S ∅ ≠ R) → stemGap G s R = 0) :
    (∑ S ∈ F, (criticalVertices G S ∩ stemBlock G s).card) =
    ∑ S ∈ F, (stemBlock G s \ S).card := by
  classical
  let O := F.filter fun S => s ∉ S
  let P := F.filter fun S => s ∈ S
  let f := fun S => stemSwap G s S ∅
  let I := O.image f
  have hOP : Disjoint O P := by
    rw [disjoint_left]
    intro S hSO hSP
    exact (mem_filter.mp hSO).2 (mem_filter.mp hSP).2
  have hF : O ∪ P = F := by
    ext S; simp [O, P]; tauto
  have hfmem (S : Finset V) (hS : S ∈ O) : f S ∈ P := by
    rcases mem_filter.mp hS with ⟨hSF, hs⟩
    exact mem_filter.mpr ⟨hclosed S hSF hs, mem_union_left _ (mem_insert_self _ _)⟩
  have hIP : I ⊆ P := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hT
    exact hfmem S hS
  have hinj : Set.InjOn f (O : Set (Finset V)) := by
    intro S hS R hR heq
    rcases mem_filter.mp hS with ⟨hSF, hsS⟩
    rcases mem_filter.mp hR with ⟨hRF, hsR⟩
    exact (stemSwap_injective G (hdom S hSF) (hdom R hRF)
      hsS hsR (empty_subset _) (empty_subset _) heq).1
  have hsumI : ∑ S ∈ I, stemGap G s S = - ∑ S ∈ O, stemGap G s S := by
    rw [show I = O.image f from rfl, sum_image hinj, ← sum_neg_distrib]
    apply sum_congr rfl
    intro S hS
    rcases mem_filter.mp hS with ⟨hSF, hs⟩
    exact stemGap_empty_swap G (hdom S hSF) hs hL
  have hrem : (∑ S ∈ P \ I, stemGap G s S) = 0 := by
    apply sum_eq_zero
    intro R hR
    rcases mem_sdiff.mp hR with ⟨hRP, hRI⟩
    rcases mem_filter.mp hRP with ⟨hRF, hsR⟩
    apply hzero R hRF hsR
    intro S hSF hsS heq
    exact hRI (mem_image.mpr ⟨S, mem_filter.mpr ⟨hSF, hsS⟩, heq⟩)
  have hsumP : ∑ S ∈ P, stemGap G s S =
      (∑ S ∈ P \ I, stemGap G s S) + ∑ S ∈ I, stemGap G s S :=
    (sum_sdiff hIP).symm
  have hgap : (∑ S ∈ F, stemGap G s S) = 0 := by
    rw [← hF, sum_union hOP, hsumP, hsumI, hrem]
    ring
  simp only [stemGap, sum_sub_distrib] at hgap
  exact_mod_cast (sub_eq_zero.mp hgap).symm

/-- Star-like blocks with one or two leaves attain exact local balance. -/
theorem activeStemFamily_eq_of_starLike (s : V) (hstar : StarLike G)
    (hk : leafCount G s = 1 ∨ leafCount G s = 2) :
    (∑ S ∈ activeStemFamily G s, (criticalVertices G S ∩ stemBlock G s).card) =
    ∑ S ∈ activeStemFamily G s, (stemBlock G s \ S).card := by
  classical
  have hL : (leafNeighbors G s).Nonempty := by
    apply card_pos.mp
    change 0 < leafCount G s
    rcases hk with h | h <;> omega
  apply active_stem_family_eq G s (activeStemFamily G s) hL
  · intro S hS
    exact mem_domSets.mp (mem_filter.mp hS).1
  · intro S hS _
    exact empty_stemSwap_mem_active G hL hS
  · intro R hR hsR hnotimage
    have hdomR := mem_domSets.mp (mem_filter.mp hR).1
    have hactive := (mem_filter.mp hR).2
    have hLn : ¬ leafNeighbors G s ⊆ R := by
      intro h; exact hactive (insert_subset_iff.mpr ⟨hsR, h⟩)
    have hmiss : (leafNeighbors G s \ R).Nonempty := by
      obtain ⟨x, hx, hxR⟩ := not_subset.mp hLn
      exact ⟨x, mem_sdiff.mpr ⟨hx, hxR⟩⟩
    have hcount : (leafNeighbors G s \ R).card = 1 := by
      have hpos := card_pos.mpr hmiss
      rcases hk with hk | hk
      · have hle := card_le_card (sdiff_subset : leafNeighbors G s \ R ⊆ leafNeighbors G s)
        change leafCount G s = 1 at hk
        change (leafNeighbors G s).card = 1 at hk
        omega
      · have hinter : (R ∩ leafNeighbors G s).Nonempty := by
          by_contra hnon
          have hemp := not_nonempty_iff_eq_empty.mp hnon
          obtain ⟨S, hS, hsS, heq⟩ := emptyLeaf_predecessor_starLike G hstar hk hdomR hsR hemp
          exact hnotimage S hS hsS heq
        have hipos := card_pos.mpr hinter
        have hsum := card_sdiff_add_card_inter (leafNeighbors G s) R
        rw [inter_comm] at hsum
        change (leafNeighbors G s).card = 2 at hk
        omega
    rw [stemGap, critical_inter_block_stem_mem G hdomR hsR hLn,
      block_sdiff_stem_mem G hsR, hcount, card_singleton]
    simp

end D5.S3.Combinatorics.Graph.DominatingSetAverageBoundStem
