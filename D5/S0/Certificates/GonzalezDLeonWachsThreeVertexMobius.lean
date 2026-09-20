/- GID: D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius
   generality: I
   mirror-B: D5/B/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius
   mirror-E: none(waiver:kernel-checked-source-evaluation)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.result; premises=D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius.triangle_three_source_mobius_polynomial,D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius.path_three_source_mobius_polynomial
   digest: Exact incidence-algebra Mobius polynomials for the triangle and path source posets. -/

import D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.GonzalezDLeonWachsThreeVertexMobius

open Finset
open D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource

noncomputable section

private theorem finThreePartition_eq_bot_of_card_three
    (P : Finpartition (univ : Finset (Fin 3))) (hcard : P.parts.card = 3) :
    P = ⊥ := by
  have hsingle : ∀ block ∈ P.parts, ∃ vertex : Fin 3, block = {vertex} := by
    intro block hb
    have hupper := fin_three_partition_block_card_le P hb
    have hpositive := Finset.card_pos.mpr (P.nonempty_of_mem_parts hb)
    have hblockcard : block.card = 1 := by omega
    exact Finset.card_eq_one.mp hblockcard
  apply Finpartition.ext
  ext block
  constructor
  · intro hb
    obtain ⟨vertex, rfl⟩ := hsingle block hb
    exact Finpartition.mem_bot_iff.mpr ⟨vertex, mem_univ _, rfl⟩
  · intro hb
    obtain ⟨vertex, _, rfl⟩ := Finpartition.mem_bot_iff.mp hb
    obtain ⟨part, hp, hv⟩ := P.exists_mem (mem_univ vertex)
    obtain ⟨other, heq⟩ := hsingle part hp
    have : vertex = other := by simpa [heq] using hv
    subst other
    exact heq ▸ hp

private theorem finThreePartition_eq_indiscrete_of_card_one
    (P : Finpartition (univ : Finset (Fin 3))) (hcard : P.parts.card = 1) :
    P = Finpartition.indiscrete Finset.univ_nonempty.ne_empty := by
  obtain ⟨block, hparts⟩ := Finset.card_eq_one.mp hcard
  have huniv : block = (univ : Finset (Fin 3)) := by
    have hsum := P.sum_card_parts
    rw [hparts, Finset.sum_singleton] at hsum
    have hsub : block ⊆ (univ : Finset (Fin 3)) := subset_univ _
    exact Finset.eq_of_subset_of_card_le hsub (by simpa using hsum.ge)
  apply Finpartition.ext
  simp [hparts, huniv]

private theorem finThreePartition_exists_pair_of_card_two
    (P : Finpartition (univ : Finset (Fin 3))) (hcard : P.parts.card = 2) :
    ∃ block ∈ P.parts, block.card = 2 := by
  by_contra hnone
  push Not at hnone
  have hsingle : ∀ block ∈ P.parts, block.card = 1 := by
    intro block hb
    have hupper := fin_three_partition_block_card_le P hb
    have hpos := Finset.card_pos.mpr (P.nonempty_of_mem_parts hb)
    have hne := hnone block hb
    omega
  have hsum : (∑ block ∈ P.parts, block.card) = P.parts.card := by
    calc
      (∑ block ∈ P.parts, block.card) = ∑ _block ∈ P.parts, 1 := by
        exact Finset.sum_congr rfl hsingle
      _ = P.parts.card := by simp
  rw [P.sum_card_parts] at hsum
  simp only [Finset.card_univ, Fintype.card_fin, hcard] at hsum
  omega

private theorem finThreePartition_pair_complement
    (P : Finpartition (univ : Finset (Fin 3)))
    (hcard : P.parts.card = 2) {block : Finset (Fin 3)}
    (hblock : block ∈ P.parts) :
    P.parts = {block, (univ : Finset (Fin 3)) \ block} := by
  obtain ⟨a, b, hab, hpairs⟩ := Finset.card_eq_two.mp hcard
  have hchoice : block = a ∨ block = b := by
    rw [hpairs] at hblock
    simpa using hblock
  let other := if block = a then b else a
  have hother : other ∈ P.parts := by
    rcases hchoice with ha | hb
    · simp [other, ha, hpairs]
    · have hba : block ≠ a := by
        intro heq
        exact hab (heq.symm.trans hb)
      simp [other, hba, hpairs]
  have hne : block ≠ other := by
    rcases hchoice with ha | hb
    · simp [other, ha, hab]
    · have hba : block ≠ a := by
        intro heq
        exact hab (heq.symm.trans hb)
      simp [other, hb, hab.symm]
  have hparts : P.parts = {block, other} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro part hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hblock
      · exact hother
    · simp [hne, hcard]
  have hcomplement : other = (univ : Finset (Fin 3)) \ block := by
    ext vertex
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hv hvblock
      exact Finset.disjoint_left.mp (P.disjoint hother hblock hne.symm) hv hvblock
    · intro hvnot
      obtain ⟨part, hp, hv⟩ := P.exists_mem (mem_univ vertex)
      rw [hparts] at hp
      rcases Finset.mem_insert.mp hp with heq | heq
      · exact False.elim (hvnot (heq ▸ hv))
      · exact (Finset.mem_singleton.mp heq) ▸ hv
  rw [hparts, hcomplement]

private theorem localEdge_of_connected_pair
    {G : SimpleGraph (Fin 3)} {block : Finset (Fin 3)}
    (hpair : block.card = 2)
    (hconnected : (G.induce (block : Set (Fin 3))).Connected) :
    ∃ edge : LocalEdge G, localEdgeBlock edge = block := by
  obtain ⟨left, right, hne, hblock⟩ := Finset.card_eq_two.mp hpair
  have hset : (block : Set (Fin 3)) = {left, right} := by
    ext vertex
    simp [hblock]
  rw [hset] at hconnected
  have : Nontrivial ({left, right} : Set (Fin 3)) :=
    ⟨⟨⟨left, by simp⟩, ⟨right, by simp⟩, by
      intro heq
      exact hne (congrArg Subtype.val heq)⟩⟩
  obtain ⟨neighbor, hadj⟩ := hconnected.preconnected.exists_adj_of_nontrivial
    (⟨left, by simp⟩ : ({left, right} : Set (Fin 3)))
  have hright : neighbor.val = right := by
    have hmember : neighbor.val = left ∨ neighbor.val = right := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using neighbor.property
    rcases hmember with hleft | hright
    · exact False.elim (hadj.ne (Subtype.ext hleft.symm))
    · exact hright
  have hadj' : G.Adj left right := by
    simpa [hright] using hadj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨⟨left, right, hlt, hadj'⟩, ?_⟩
    simp [localEdgeBlock, hblock]
  · refine ⟨⟨right, left, hgt, hadj'.symm⟩, ?_⟩
    simp [localEdgeBlock, hblock, Finset.pair_comm]

private theorem localNormalFormToSource_surjective
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    Function.Surjective (localNormalFormToSource hG) := by
  intro P
  let p := P.val.partition
  have hpos : 0 < p.parts.card :=
    Finset.card_pos.mpr (p.parts_nonempty Finset.univ_nonempty.ne_empty)
  have hupper : p.parts.card ≤ 3 := by
    simpa [p] using p.card_parts_le_card
  by_cases hcount : p.parts.card = 1
  · have hpartition : P.val.partition =
        Finpartition.indiscrete Finset.univ_nonempty.ne_empty :=
        finThreePartition_eq_indiscrete_of_card_one _ hcount
    have hmem : (univ : Finset (Fin 3)) ∈ P.val.partition.parts := by
      rw [hpartition]
      simp
    let w : Fin 3 := ⟨P.val.weight univ,
      by simpa using P.val.weight_lt_card univ hmem⟩
    refine ⟨.top w, ?_⟩
    apply Subtype.ext
    change localTopWeighted w = P.val
    symm
    apply WeightedPartition.ext hpartition
    funext block
    by_cases hb : block = (univ : Finset (Fin 3))
    · subst block
      apply Fin.ext
      rfl
    · have hnot : block ∉ P.val.partition.parts := by
        rw [hpartition]
        simpa using hb
      rw [P.val.weight_eq_zero block hnot]
      simp [localTopWeighted, hb]
  · by_cases hcount2 : p.parts.card = 2
    · obtain ⟨block, hblock, hcard⟩ :=
        finThreePartition_exists_pair_of_card_two p hcount2
      obtain ⟨edge, hedge⟩ := localEdge_of_connected_pair hcard (P.property block hblock)
      have hparts := finThreePartition_pair_complement p hcount2 hblock
      have hpartition : P.val.partition = localMiddlePartition edge := by
        apply Finpartition.ext
        rw [hparts, ← hedge]
        rfl
      let w : Fin 2 := ⟨P.val.weight block,
        by simpa [hcard] using P.val.weight_lt_card block hblock⟩
      refine ⟨.middle edge w, ?_⟩
      apply Subtype.ext
      change localMiddleWeighted edge w = P.val
      symm
      apply WeightedPartition.ext hpartition
      funext part
      by_cases heq : part = block
      · subst part
        apply Fin.ext
        simp [localMiddleWeighted, hedge, w]
      · have hother : part ∈ P.val.partition.parts →
            part = (univ : Finset (Fin 3)) \ block := by
          rw [hparts]
          simp [heq]
        have hzero : P.val.weight part = 0 := by
          by_cases hp : part ∈ P.val.partition.parts
          · have hpart : part = (univ : Finset (Fin 3)) \ block := hother hp
            have hsize : part.card = 1 := by
              rw [hpart, Finset.card_sdiff, Finset.inter_eq_left.mpr (subset_univ _),
                Finset.card_univ, Fintype.card_fin, hcard]
            have hbound := P.val.weight_lt_card part hp
            apply Fin.ext
            simp only [Fin.val_zero]
            omega
          · exact P.val.weight_eq_zero part hp
        rw [hzero]
        simp [localMiddleWeighted, hedge, heq]
    · have hcount3 : p.parts.card = 3 := by omega
      have hpartition : P.val.partition = ⊥ :=
        finThreePartition_eq_bot_of_card_three _ hcount3
      refine ⟨.bottom, ?_⟩
      apply Subtype.ext
      change weightedBottom (Fin 3) = P.val
      symm
      apply WeightedPartition.ext hpartition
      funext block
      by_cases hb : block ∈ P.val.partition.parts
      · have hsingleton : ∃ vertex : Fin 3, block = {vertex} := by
          rw [hpartition] at hb
          obtain ⟨vertex, _, heq⟩ := Finpartition.mem_bot_iff.mp hb
          exact ⟨vertex, heq.symm⟩
        obtain ⟨vertex, heq⟩ := hsingleton
        have hsize : block.card = 1 := by rw [heq]; simp
        have hbound := P.val.weight_lt_card block hb
        rw [hsize] at hbound
        apply Fin.ext
        change (P.val.weight block : Nat) = 0
        omega
      · rw [P.val.weight_eq_zero block hb]
        rfl

private instance localNormalFormPartialOrder
    (G : SimpleGraph (Fin 3)) [Fact G.Connected] :
    PartialOrder (LocalNormalForm G) where
  le := fun left right =>
    localNormalFormToSource Fact.out left ≤ localNormalFormToSource Fact.out right
  lt := fun left right =>
    localNormalFormToSource Fact.out left < localNormalFormToSource Fact.out right
  le_refl _ := le_refl _
  le_trans _ _ _ := le_trans
  le_antisymm _ _ hleft hright :=
    local_normal_form_to_source_injective Fact.out (le_antisymm hleft hright)
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

private def localNormalFormOrderIso
    (G : SimpleGraph (Fin 3)) [Fact G.Connected] :
    LocalNormalForm G ≃o ConnectedWeightedPartition G := by
  let hG : G.Connected := Fact.out
  exact {
    toFun := localNormalFormToSource hG
    invFun := Function.surjInv (localNormalFormToSource_surjective hG)
    left_inv := Function.leftInverse_surjInv
      ⟨local_normal_form_to_source_injective hG, localNormalFormToSource_surjective hG⟩
    right_inv := Function.rightInverse_surjInv (localNormalFormToSource_surjective hG)
    map_rel_iff' := Iff.rfl }

private theorem local_middle_le_top_iff
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) (j : Fin 3) :
    (localNormalFormToSource hG (.middle edge w) ≤
      localNormalFormToSource hG (.top j)) ↔
      (w : Nat) ≤ j ∧ (j : Nat) ≤ w + 1 := by
  have hparts : (localMiddlePartition edge).parts.card = 2 := by
    simp [localMiddlePartition, localEdgeBlock_ne_compl edge]
  have htop : (localTopWeighted j).partition.parts =
      {(univ : Finset (Fin 3))} := rfl
  have hchildrenSet : children (localMiddlePartition edge)
      (univ : Finset (Fin 3)) = (localMiddlePartition edge).parts.attach := by
    ext lower
    simp [children]
  have hchildren : (children (localMiddlePartition edge)
      (univ : Finset (Fin 3))).card = 2 := by
    rw [hchildrenSet, Finset.card_attach, hparts]
  have hweight : totalBlockWeight (localMiddleWeighted edge w) = (w : Nat) := by
    have hedge : localEdgeBlock edge ≠ ∅ := by
      intro hzero
      have hcard : (localEdgeBlock edge).card = 2 := by
        simp [localEdgeBlock, ne_of_lt edge.left_lt_right]
      rw [hzero, Finset.card_empty] at hcard
      omega
    simp [totalBlockWeight, localMiddleWeighted, localMiddlePartition,
      localEdgeBlock_ne_compl edge, hedge, Finset.univ_nonempty.ne_empty]
  have hsum : childWeightSum (localMiddleWeighted edge w) univ = (w : Nat) := by
    calc
      _ = totalBlockWeight (localMiddleWeighted edge w) := by
        unfold childWeightSum totalBlockWeight
        change (∑ lower ∈ children (localMiddlePartition edge) univ,
          ((localMiddleWeighted edge w).weight lower : Nat)) = _
        rw [hchildrenSet]
        exact Finset.sum_attach (localMiddleWeighted edge w).partition.parts
          (fun block : Finset (Fin 3) =>
            ((localMiddleWeighted edge w).weight block : Nat))
      _ = (w : Nat) := hweight
  constructor
  · intro hle
    change WeightedRefines (localMiddleWeighted edge w) (localTopWeighted j) at hle
    rcases hle.2 ⟨univ, by simp [localTopWeighted]⟩ with ⟨d, hd, heq⟩
    change d < (children (localMiddlePartition edge) univ).card at hd
    change (j : Nat) = childWeightSum (localMiddleWeighted edge w) univ + d at heq
    rw [hchildren] at hd
    rw [hsum] at heq
    omega
  · rintro ⟨hlo, hhi⟩
    change WeightedRefines (localMiddleWeighted edge w) (localTopWeighted j)
    refine ⟨?_, ?_⟩
    · exact le_top
    · intro upper
      have hupper : upper.val = (univ : Finset (Fin 3)) := by
        simpa [localTopWeighted] using upper.property
      refine ⟨(j : Nat) - w, ?_, ?_⟩
      · change (j : Nat) - w <
            (children (localMiddlePartition edge) upper.val).card
        rw [hupper, hchildren]
        omega
      · rw [hupper]
        rw [hsum]
        simp [localTopWeighted]
        omega

private theorem local_middle_le_middle_iff
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge other : LocalEdge G) (w v : Fin 2) :
    (localNormalFormToSource hG (.middle edge w) ≤
      localNormalFormToSource hG (.middle other v)) ↔
      edge = other ∧ w = v := by
  constructor
  · intro hle
    change WeightedRefines (localMiddleWeighted edge w)
      (localMiddleWeighted other v) at hle
    have hmem : localEdgeBlock edge ∈ (localMiddlePartition edge).parts := by
      simp [localMiddlePartition]
    obtain ⟨upper, hu, hsub⟩ := hle.1 hmem
    have htarget : upper = localEdgeBlock other ∨
        upper = (univ : Finset (Fin 3)) \ localEdgeBlock other := by
      change upper ∈ (localMiddlePartition other).parts at hu
      simpa [localMiddlePartition] using hu
    have hblock : localEdgeBlock edge = localEdgeBlock other := by
      rcases htarget with heq | heq
      · exact Finset.eq_of_subset_of_card_le (heq ▸ hsub) (by
          simp [localEdgeBlock, ne_of_lt edge.left_lt_right,
            ne_of_lt other.left_lt_right])
      · have hsize := Finset.card_le_card hsub
        have hedgecard : (localEdgeBlock edge).card = 2 := by
          simp [localEdgeBlock, ne_of_lt edge.left_lt_right]
        have hothercard : (localEdgeBlock other).card = 2 := by
          simp [localEdgeBlock, ne_of_lt other.left_lt_right]
        rw [heq, hedgecard, Finset.card_sdiff,
          Finset.inter_eq_left.mpr (subset_univ _), Finset.card_univ,
          Fintype.card_fin, hothercard] at hsize
        omega
    have hedges : edge = other := local_edge_eq_of_block_eq hblock
    subst other
    have heq : localMiddleWeighted edge w = localMiddleWeighted edge v :=
      weighted_refines_eq_of_partition_eq hle rfl
    have hweights := congrArg
      (fun P : WeightedPartition (Fin 3) => (P.weight (localEdgeBlock edge) : Nat)) heq
    simp only [localMiddleWeighted, ite_true] at hweights
    exact ⟨rfl, Fin.ext hweights⟩
  · rintro ⟨rfl, rfl⟩
    exact le_refl _

private theorem local_top_le_top_iff
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (w v : Fin 3) :
    (localNormalFormToSource hG (.top w) ≤
      localNormalFormToSource hG (.top v)) ↔ w = v := by
  constructor
  · intro hle
    change WeightedRefines (localTopWeighted w) (localTopWeighted v) at hle
    have heq := weighted_refines_eq_of_partition_eq hle rfl
    have hweights := congrArg
      (fun P : WeightedPartition (Fin 3) => (P.weight (univ : Finset (Fin 3)) : Nat)) heq
    simp only [localTopWeighted, ite_true] at hweights
    exact Fin.ext hweights
  · rintro rfl
    exact le_refl _

private theorem local_top_not_le_middle
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (w : Fin 3) (edge : LocalEdge G) (v : Fin 2) :
    ¬localNormalFormToSource hG (.top w) ≤
      localNormalFormToSource hG (.middle edge v) := by
  intro hle
  have hcard := Finpartition.card_mono hle.1
  change (localMiddlePartition edge).parts.card ≤
    (localTopWeighted w).partition.parts.card at hcard
  simp [localMiddlePartition, localEdgeBlock_ne_compl edge,
    localTopWeighted] at hcard

private theorem local_middle_not_le_bottom
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) :
    ¬localNormalFormToSource hG (.middle edge w) ≤
      localNormalFormToSource hG .bottom := by
  intro hle
  have hcard := Finpartition.card_mono hle.1
  change (⊥ : Finpartition (univ : Finset (Fin 3))).parts.card ≤
    (localMiddlePartition edge).parts.card at hcard
  simp [localMiddlePartition, localEdgeBlock_ne_compl edge] at hcard

private theorem local_top_not_le_bottom
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (w : Fin 3) :
    ¬localNormalFormToSource hG (.top w) ≤
      localNormalFormToSource hG .bottom := by
  intro hle
  have hcard := Finpartition.card_mono hle.1
  change (⊥ : Finpartition (univ : Finset (Fin 3))).parts.card ≤
    (localTopWeighted w).partition.parts.card at hcard
  simp [localTopWeighted] at hcard

private theorem local_top_isMax
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (w : Fin 3) :
    IsMax (localNormalFormToSource hG (.top w)) := by
  intro Q hle
  have hcard := Finpartition.card_mono hle.1
  change Q.val.partition.parts.card ≤ (localTopWeighted w).partition.parts.card at hcard
  have hpositive : 0 < Q.val.partition.parts.card :=
    Finset.card_pos.mpr
      (Q.val.partition.parts_nonempty Finset.univ_nonempty.ne_empty)
  have htop : Q.val.partition =
      Finpartition.indiscrete Finset.univ_nonempty.ne_empty := by
    apply finThreePartition_eq_indiscrete_of_card_one
    simp [localTopWeighted] at hcard
    omega
  have heq : localTopWeighted w = Q.val :=
    weighted_refines_eq_of_partition_eq hle htop.symm
  change Q.val ≤ localTopWeighted w
  rw [← heq]

private theorem local_isMax_iff_top
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (normal : LocalNormalForm G) :
    IsMax (localNormalFormToSource hG normal) ↔
      ∃ w : Fin 3, normal = .top w := by
  cases normal with
  | bottom =>
      constructor
      · intro hmax
        have hle : localNormalFormToSource hG .bottom ≤
            localNormalFormToSource hG (.top 0) := bot_le
        have heq := le_antisymm hle (hmax hle)
        have hcard := congrArg (fun P : ConnectedWeightedPartition G =>
          P.val.partition.parts.card) heq
        simp [localNormalFormToSource, connectedWeightedBottom, weightedBottom,
          localTopWeighted] at hcard
      · rintro ⟨w, h⟩
        cases h
  | middle edge w =>
      constructor
      · intro hmax
        let j : Fin 3 := ⟨w, lt_trans w.isLt (by decide : 2 < 3)⟩
        have hle : localNormalFormToSource hG (.middle edge w) ≤
            localNormalFormToSource hG (.top j) :=
          (local_middle_le_top_iff hG edge w j).mpr (by dsimp [j]; omega)
        have heq := le_antisymm hle (hmax hle)
        have hcard := congrArg (fun P : ConnectedWeightedPartition G =>
          P.val.partition.parts.card) heq
        simp [localNormalFormToSource, localMiddleWeighted, localMiddlePartition,
          localEdgeBlock_ne_compl edge, localTopWeighted] at hcard
      · rintro ⟨v, h⟩
        cases h
  | top w =>
      constructor
      · intro _
        exact ⟨w, rfl⟩
      · intro _
        exact local_top_isMax hG w

private theorem local_bottom_lt_middle
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) :
    (⊥ : ConnectedWeightedPartition G) <
      localNormalFormToSource hG (.middle edge w) := by
  refine lt_of_le_of_ne bot_le ?_
  intro heq
  have hcard := congrArg (fun P : ConnectedWeightedPartition G =>
    P.val.partition.parts.card) heq
  change (localNormalFormToSource hG (LocalNormalForm.bottom)).val.partition.parts.card =
    (localNormalFormToSource hG (LocalNormalForm.middle edge w)).val.partition.parts.card
    at hcard
  simp [localNormalFormToSource, connectedWeightedBottom, weightedBottom,
    localMiddleWeighted, localMiddlePartition,
    localEdgeBlock_ne_compl edge] at hcard

private theorem local_Ico_bottom_middle
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) :
    Finset.Ico (⊥ : ConnectedWeightedPartition G)
      (localNormalFormToSource hG (.middle edge w)) = {⊥} := by
  ext P
  simp only [Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hlt⟩
    obtain ⟨normal, rfl⟩ := localNormalFormToSource_surjective hG P
    cases normal with
    | bottom => rfl
    | middle other v =>
        have heq := (local_middle_le_middle_iff hG other edge v w).mp hlt.le
        rcases heq with ⟨rfl, rfl⟩
        exact False.elim (lt_irrefl _ hlt)
    | top v => exact False.elim (local_top_not_le_middle hG v edge w hlt.le)
  · rintro rfl
    exact ⟨le_refl _, local_bottom_lt_middle hG edge w⟩

private theorem local_mu_bottom_middle
    {G : SimpleGraph (Fin 3)} (hG : G.Connected)
    (edge : LocalEdge G) (w : Fin 2) :
    (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G)
      (localNormalFormToSource hG (.middle edge w)) = -1 := by
  have hne : (⊥ : ConnectedWeightedPartition G) ≠
      localNormalFormToSource hG (.middle edge w) :=
    ne_of_lt (local_bottom_lt_middle hG edge w)
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne,
    local_Ico_bottom_middle hG edge w, Finset.sum_singleton,
    IncidenceAlgebra.mu_self]

private def localEligibleMiddle
    (G : SimpleGraph (Fin 3)) (j : Fin 3) : Finset (LocalEdge G × Fin 2) :=
  Finset.univ.filter fun ew => (ew.2 : Nat) ≤ j ∧ (j : Nat) ≤ ew.2 + 1

private theorem local_Ico_bottom_top
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (j : Fin 3) :
    Finset.Ico (⊥ : ConnectedWeightedPartition G)
      (localNormalFormToSource hG (.top j)) =
      insert (⊥ : ConnectedWeightedPartition G)
        ((localEligibleMiddle G j).image fun ew =>
          localNormalFormToSource hG (.middle ew.1 ew.2)) := by
  ext P
  simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨_, hlt⟩
    obtain ⟨normal, rfl⟩ := localNormalFormToSource_surjective hG P
    cases normal with
    | bottom => exact Or.inl rfl
    | middle edge w =>
        refine Or.inr ⟨(edge, w), ?_, rfl⟩
        simpa [localEligibleMiddle] using
          (local_middle_le_top_iff hG edge w j).mp hlt.le
    | top w =>
        have heq := (local_top_le_top_iff hG w j).mp hlt.le
        subst j
        exact False.elim (lt_irrefl _ hlt)
  · rintro (heq | ⟨⟨edge, w⟩, hpair, heq⟩)
    · subst P
      exact ⟨le_refl _, by
        have hcard : (⊥ : ConnectedWeightedPartition G) ≠
            localNormalFormToSource hG (.top j) := by
          intro h
          have hc := congrArg (fun Q : ConnectedWeightedPartition G =>
            Q.val.partition.parts.card) h
          change (localNormalFormToSource hG LocalNormalForm.bottom).val.partition.parts.card =
            (localNormalFormToSource hG (LocalNormalForm.top j)).val.partition.parts.card
            at hc
          simp [localNormalFormToSource, connectedWeightedBottom, weightedBottom,
            localTopWeighted] at hc
        exact lt_of_le_of_ne bot_le hcard⟩
    · subst P
      have heligible : (w : Nat) ≤ j ∧ (j : Nat) ≤ w + 1 := by
        simpa [localEligibleMiddle] using hpair
      exact ⟨bot_le, lt_of_le_of_ne
        ((local_middle_le_top_iff hG edge w j).mpr heligible) (by
          intro heq
          have hc := congrArg (fun Q : ConnectedWeightedPartition G =>
            Q.val.partition.parts.card) heq
          simp [localNormalFormToSource, localMiddleWeighted, localMiddlePartition,
            localEdgeBlock_ne_compl edge, localTopWeighted] at hc)⟩

private theorem local_mu_bottom_top
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (j : Fin 3) :
    (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G)
      (localNormalFormToSource hG (.top j)) =
      (localEligibleMiddle G j).card - 1 := by
  let imageMiddle (ew : LocalEdge G × Fin 2) :=
    localNormalFormToSource hG (LocalNormalForm.middle ew.1 ew.2)
  have hne : (⊥ : ConnectedWeightedPartition G) ≠
      localNormalFormToSource hG (.top j) := by
    intro heq
    have hc := congrArg (fun Q : ConnectedWeightedPartition G =>
      Q.val.partition.parts.card) heq
    change (localNormalFormToSource hG LocalNormalForm.bottom).val.partition.parts.card =
      (localNormalFormToSource hG (LocalNormalForm.top j)).val.partition.parts.card at hc
    simp [localNormalFormToSource, connectedWeightedBottom, weightedBottom,
      localTopWeighted] at hc
  have hnotmem : (⊥ : ConnectedWeightedPartition G) ∉
      (localEligibleMiddle G j).image imageMiddle := by
    intro hmem
    obtain ⟨⟨edge, w⟩, _, heq⟩ := Finset.mem_image.mp hmem
    have hc := congrArg (fun Q : ConnectedWeightedPartition G =>
      Q.val.partition.parts.card) heq
    change (localNormalFormToSource hG (LocalNormalForm.middle edge w)).val.partition.parts.card =
      (localNormalFormToSource hG LocalNormalForm.bottom).val.partition.parts.card at hc
    simp [localNormalFormToSource, connectedWeightedBottom, weightedBottom,
      localMiddleWeighted, localMiddlePartition,
      localEdgeBlock_ne_compl edge] at hc
  have hinj : Set.InjOn imageMiddle (localEligibleMiddle G j : Set _) := by
    intro a _ b _ hab
    have h := local_normal_form_to_source_injective hG hab
    cases a with
    | mk edge w =>
        cases b with
        | mk other v =>
            injection h with he hw
            cases he
            cases hw
            rfl
  have hsum : ∑ ew ∈ localEligibleMiddle G j,
        (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) (imageMiddle ew) =
      -((localEligibleMiddle G j).card : ℤ) := by
    calc
      _ = ∑ _ew ∈ localEligibleMiddle G j, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro ⟨edge, w⟩ _
        exact local_mu_bottom_middle hG edge w
      _ = -((localEligibleMiddle G j).card : ℤ) := by simp
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne,
    local_Ico_bottom_top hG j, Finset.sum_insert hnotmem,
    IncidenceAlgebra.mu_self]
  change -(1 + ∑ P ∈ (localEligibleMiddle G j).image imageMiddle,
    (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) P) = _
  rw [Finset.sum_image hinj, hsum]
  ring

private theorem localEligibleMiddle_card
    (G : SimpleGraph (Fin 3)) (j : Fin 3) :
    (localEligibleMiddle G j).card =
      (if (j : Nat) = 1 then 2 else 1) * Fintype.card (LocalEdge G) := by
  fin_cases j
  · have heq : localEligibleMiddle G 0 =
        (Finset.univ : Finset (LocalEdge G)).product ({0} : Finset (Fin 2)) := by
      ext ⟨edge, w⟩
      fin_cases w <;> simp [localEligibleMiddle]
    simp [heq]
  · have heq : localEligibleMiddle G 1 =
        (Finset.univ : Finset (LocalEdge G)).product (Finset.univ : Finset (Fin 2)) := by
      ext ⟨edge, w⟩
      fin_cases w <;> simp [localEligibleMiddle]
    simp [heq, Fintype.card_fin, mul_comm]
  · have heq : localEligibleMiddle G 2 =
        (Finset.univ : Finset (LocalEdge G)).product ({1} : Finset (Fin 2)) := by
      ext ⟨edge, w⟩
      fin_cases w <;> simp [localEligibleMiddle]
    simp [heq]

private theorem localEdge_endpoints {G : SimpleGraph (Fin 3)} (edge : LocalEdge G) :
    (edge.left = 0 ∧ edge.right = 1) ∨
    (edge.left = 0 ∧ edge.right = 2) ∨
    (edge.left = 1 ∧ edge.right = 2) := by
  cases edge with
  | mk left right hlt hadj =>
      fin_cases left <;> fin_cases right <;> simp_all <;> norm_num at hlt

private def triangleEdge01 : LocalEdge triangleThree :=
  ⟨0, 1, by decide, by simp [triangleThree]⟩

private def triangleEdge02 : LocalEdge triangleThree :=
  ⟨0, 2, by decide, by simp [triangleThree]⟩

private def triangleEdge12 : LocalEdge triangleThree :=
  ⟨1, 2, by decide, by simp [triangleThree]⟩

private def pathEdge01 : LocalEdge pathThree :=
  ⟨0, 1, by decide, by simp [pathThree, SimpleGraph.pathGraph_adj]⟩

private def pathEdge12 : LocalEdge pathThree :=
  ⟨1, 2, by decide, by simp [pathThree, SimpleGraph.pathGraph_adj]⟩

private theorem triangleThree_edge_count : Fintype.card (LocalEdge triangleThree) = 3 := by
  have huniv : (Finset.univ : Finset (LocalEdge triangleThree)) =
      {triangleEdge01, triangleEdge02, triangleEdge12} := by
    ext edge
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases localEdge_endpoints edge with h | h | h
    · exact Or.inl (LocalEdge.ext h.1 h.2)
    · exact Or.inr (Or.inl (LocalEdge.ext h.1 h.2))
    · exact Or.inr (Or.inr (LocalEdge.ext h.1 h.2))
  have h01ne02 : triangleEdge01 ≠ triangleEdge02 := by
    intro h
    have hc := congrArg LocalEdge.right h
    exact (by decide : (1 : Fin 3) ≠ 2) hc
  have h01ne12 : triangleEdge01 ≠ triangleEdge12 := by
    intro h
    have hc := congrArg LocalEdge.left h
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  have h02ne12 : triangleEdge02 ≠ triangleEdge12 := by
    intro h
    have hc := congrArg LocalEdge.left h
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  change (Finset.univ : Finset (LocalEdge triangleThree)).card = 3
  rw [huniv]
  simp [h01ne02, h01ne12, h02ne12]

private theorem pathThree_edge_count : Fintype.card (LocalEdge pathThree) = 2 := by
  have huniv : (Finset.univ : Finset (LocalEdge pathThree)) =
      {pathEdge01, pathEdge12} := by
    ext edge
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases localEdge_endpoints edge with h | h | h
    · exact Or.inl (LocalEdge.ext h.1 h.2)
    · have hn : ¬pathThree.Adj (0 : Fin 3) 2 := by
        simp [pathThree, SimpleGraph.pathGraph_adj]
      exact False.elim (hn (h.1 ▸ h.2 ▸ edge.adjacent))
    · exact Or.inr (LocalEdge.ext h.1 h.2)
  have hne : pathEdge01 ≠ pathEdge12 := by
    intro h
    have hc := congrArg LocalEdge.left h
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  change (Finset.univ : Finset (LocalEdge pathThree)).card = 2
  rw [huniv]
  simp [hne]

private theorem sourceMobiusPolynomial_local
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    sourceMobiusPolynomial G =
      Polynomial.C ((Fintype.card (LocalEdge G) : ℝ) - 1) +
      Polynomial.C (2 * (Fintype.card (LocalEdge G) : ℝ) - 1) * Polynomial.X +
        Polynomial.C ((Fintype.card (LocalEdge G) : ℝ) - 1) * Polynomial.X ^ 2 := by
  classical
  have hmax : (Finset.univ.filter (IsMax : ConnectedWeightedPartition G → Prop)) =
      (Finset.univ : Finset (Fin 3)).image
        (fun j => localNormalFormToSource hG (LocalNormalForm.top j)) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨normal, rfl⟩ := localNormalFormToSource_surjective hG P
      obtain ⟨j, hnormal⟩ := (local_isMax_iff_top hG normal).mp hp
      subst normal
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact local_top_isMax hG j
  have hinj : Set.InjOn
      (fun j : Fin 3 => localNormalFormToSource hG (LocalNormalForm.top j))
      (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
    intro j _ k _ h
    have hnormal := local_normal_form_to_source_injective hG h
    exact LocalNormalForm.top.inj hnormal
  unfold sourceMobiusPolynomial
  rw [hmax, Finset.sum_image hinj]
  simp only [local_mu_bottom_top, localEligibleMiddle_card]
  simp [localNormalFormToSource, totalBlockWeight, localTopWeighted]
  simp [Fin.sum_univ_succ]
  ring

theorem triangle_three_source_mobius_polynomial :
    sourceMobiusPolynomial triangleThree =
      2 + 5 * Polynomial.X + 2 * Polynomial.X ^ 2 := by
  have hconnected : triangleThree.Connected := SimpleGraph.connected_top
  rw [sourceMobiusPolynomial_local hconnected, triangleThree_edge_count]
  norm_num [Polynomial.C_eq_natCast]
  simp only [Polynomial.C_ofNat]

theorem path_three_source_mobius_polynomial :
    sourceMobiusPolynomial pathThree =
      1 + 3 * Polynomial.X + Polynomial.X ^ 2 := by
  have hconnected : pathThree.Connected := by
    simpa [pathThree] using SimpleGraph.pathGraph_connected 2
  rw [sourceMobiusPolynomial_local hconnected, pathThree_edge_count]
  norm_num [Polynomial.C_eq_natCast]
  simp only [Polynomial.C_ofNat]


end

end D5.S0.Certificates.GonzalezDLeonWachsThreeVertexMobius
