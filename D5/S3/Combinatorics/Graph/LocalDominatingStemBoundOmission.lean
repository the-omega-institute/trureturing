/- GID: D5/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LocalDominatingStemBoundOmission
   mirror-E: none(waiver:finite-combinatorial-identities)
   anchors: []
   utility: none
   digest: Omitting a stem forces its leaves and full internal domination of the residual graph. -/

import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundResidual
import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LocalDominatingStemBoundOmission

open Finset DominatingSetAverage LocalDominatingStemBoundStructure
  LocalDominatingStemBoundResidual LocalDominatingStemBoundSplit

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def domSetsWithout (G : SimpleGraph V) (v : V) : Finset (Finset V) := by
  classical
  exact (domSets G).filter (fun S => v ∉ S)

@[simp] theorem mem_domSetsWithout {G : SimpleGraph V} {v : V} {S : Finset V} :
    S ∈ domSetsWithout G v ↔ G.IsDominating (S : Set V) ∧ v ∉ S := by
  classical
  simp [domSetsWithout]

theorem omitted_stem_leaves {G : SimpleGraph V} {v : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hv : v ∉ S) : leafNeighbors G v ⊆ S := by
  intro x hx
  have hdom := (leaf_dominated_iff (mem_leafNeighbors.mp hx).2
    (mem_leafNeighbors.mp hx).1.symm S).mp (hS x)
  exact hdom.resolve_right hv

theorem omitted_stem_residual {G : SimpleGraph V} {v : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hv : v ∉ S) :
    S ∩ remaining G v ∈ residualDomSets G v := by
  classical
  refine mem_residualDomSets.mpr ⟨inter_subset_right, ?_⟩
  intro x hx
  rcases hS x with hxs | ⟨y,hy,hxy⟩
  · exact Or.inl (mem_inter.mpr ⟨hxs,hx⟩)
  · refine Or.inr ⟨y,mem_inter.mpr ⟨hy,?_⟩,hxy⟩
    refine mem_remaining.mpr ⟨fun hyv => hv (hyv ▸ hy), ?_⟩
    rintro ⟨hvy,hly⟩
    exact (mem_remaining.mp hx).1 (leaf_adj_unique hly hvy.symm hxy.symm)

theorem omitted_join_dominating {G : SimpleGraph V} {v : V} {T : Finset V}
    (hL : (leafNeighbors G v).Nonempty) (hT : T ∈ residualDomSets G v) :
    G.IsDominating ((leafNeighbors G v ∪ T : Finset V) : Set V) ∧
      v ∉ leafNeighbors G v ∪ T := by
  classical
  obtain ⟨hsub,hT⟩ := mem_residualDomSets.mp hT
  refine ⟨?_, ?_⟩
  · intro x
    by_cases hxv : x = v
    · subst x
      obtain ⟨y,hy⟩ := hL
      exact Or.inr ⟨y,mem_union_left _ hy,(mem_leafNeighbors.mp hy).1⟩
    by_cases hxL : x ∈ leafNeighbors G v
    · exact Or.inl (mem_union_left _ hxL)
    have hxR : x ∈ remaining G v := mem_remaining.mpr ⟨hxv, by simpa using hxL⟩
    rcases hT x hxR with hxs | ⟨y,hy,hxy⟩
    · exact Or.inl (mem_union_right _ hxs)
    · exact Or.inr ⟨y,mem_union_right _ hy,hxy⟩
  · simp only [mem_union, not_or]
    exact ⟨leaf_not_self G v, fun hv => (mem_remaining.mp (hsub hv)).1 rfl⟩

theorem omitted_join_inter {G : SimpleGraph V} {v : V} {T : Finset V}
    (hT : T ⊆ remaining G v) :
    (leafNeighbors G v ∪ T) ∩ remaining G v = T := by
  classical
  ext x
  simp only [mem_inter,mem_union]
  constructor
  · rintro ⟨hxL | hxT,hxR⟩
    · exact False.elim ((mem_remaining.mp hxR).2 (mem_leafNeighbors.mp hxL))
    · exact hxT
  · intro hx
    exact ⟨Or.inr hx,hT hx⟩

theorem omitted_reconstruct {G : SimpleGraph V} {v : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hv : v ∉ S) :
    leafNeighbors G v ∪ (S ∩ remaining G v) = S := by
  classical
  ext x
  simp only [mem_union,mem_inter]
  constructor
  · rintro (hx | ⟨hx,_⟩)
    · exact omitted_stem_leaves hS hv hx
    · exact hx
  · intro hx
    by_cases hxL : x ∈ leafNeighbors G v
    · exact Or.inl hxL
    · exact Or.inr ⟨hx,mem_remaining.mpr ⟨fun hxv => hv (hxv ▸ hx), by simpa using hxL⟩⟩

theorem omitted_family_card (G : SimpleGraph V) (v : V)
    (hL : (leafNeighbors G v).Nonempty) :
    (domSetsWithout G v).card = (residualDomSets G v).card := by
  classical
  symm
  refine Finset.card_bij' (fun T _ => leafNeighbors G v ∪ T)
    (fun S _ => S ∩ remaining G v) ?_ ?_ ?_ ?_
  · intro T hT
    exact mem_domSetsWithout.mpr (omitted_join_dominating hL hT)
  · intro S hS
    exact omitted_stem_residual (mem_domSetsWithout.mp hS).1 (mem_domSetsWithout.mp hS).2
  · intro T hT
    exact omitted_join_inter (mem_residualDomSets.mp hT).1
  · intro S hS
    exact omitted_reconstruct (mem_domSetsWithout.mp hS).1 (mem_domSetsWithout.mp hS).2

theorem omitted_family_sum (G : SimpleGraph V) (v : V)
    (hL : (leafNeighbors G v).Nonempty) (f : Finset V → ℚ) :
    (∑ T ∈ residualDomSets G v, f (leafNeighbors G v ∪ T)) =
      ∑ S ∈ domSetsWithout G v, f S := by
  classical
  refine Finset.sum_bij' (fun T _ => leafNeighbors G v ∪ T)
    (fun S _ => S ∩ remaining G v) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    exact mem_domSetsWithout.mpr (omitted_join_dominating hL hT)
  · intro S hS
    exact omitted_stem_residual (mem_domSetsWithout.mp hS).1 (mem_domSetsWithout.mp hS).2
  · intro T hT
    exact omitted_join_inter (mem_residualDomSets.mp hT).1
  · intro S hS
    exact omitted_reconstruct (mem_domSetsWithout.mp hS).1 (mem_domSetsWithout.mp hS).2
  · intro _ _
    rfl

theorem omitted_card_sum (G : SimpleGraph V) (v : V)
    (hL : (leafNeighbors G v).Nonempty) :
    (∑ S ∈ domSetsWithout G v, (S.card : ℚ)) =
      leafCount G v * (residualDomSets G v).card +
        ∑ T ∈ residualDomSets G v, (T.card : ℚ) := by
  classical
  rw [← omitted_family_sum G v hL (fun S => (S.card : ℚ))]
  have hcard : ∀ T ∈ residualDomSets G v,
      ((leafNeighbors G v ∪ T).card : ℚ) = leafCount G v + (T.card : ℚ) := by
    intro T hT
    have hsub := (mem_residualDomSets.mp hT).1
    have hd : Disjoint (leafNeighbors G v) T := by
      apply disjoint_left.mpr
      intro x hx hxt
      exact (mem_remaining.mp (hsub hxt)).2 (mem_leafNeighbors.mp hx)
    rw [card_union_of_disjoint hd, Nat.cast_add]
    rfl
  rw [sum_congr rfl hcard, sum_add_distrib]
  simp [mul_comm]

theorem dominating_family_partition (G : SimpleGraph V) (v : V) :
    Disjoint (domSetsAt G v) (domSetsWithout G v) ∧
      domSetsAt G v ∪ domSetsWithout G v = domSets G := by
  classical
  constructor
  · apply disjoint_left.mpr
    intro S hS hS'
    exact (mem_domSetsWithout.mp hS').2 (mem_domSetsAt.mp hS).2
  · ext S
    simp only [mem_union,mem_domSetsAt,mem_domSetsWithout,mem_domSets]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hv : v ∈ S
      · exact Or.inl ⟨h,hv⟩
      · exact Or.inr ⟨h,hv⟩

theorem dominating_total_card (G : SimpleGraph V) (v : V)
    (hL : (leafNeighbors G v).Nonempty) :
    (domSets G).card =
      2 ^ leafCount G v * (partialDomSets G v).card + (residualDomSets G v).card := by
  classical
  obtain ⟨hd,heq⟩ := dominating_family_partition G v
  rw [← heq,card_union_of_disjoint hd,stem_family_card,omitted_family_card G v hL]

theorem dominating_total_sum (G : SimpleGraph V) (v : V)
    (hL : (leafNeighbors G v).Nonempty) :
    (∑ S ∈ domSets G, (S.card : ℚ)) =
      (∑ S ∈ domSetsAt G v, (S.card : ℚ)) +
      leafCount G v * (residualDomSets G v).card +
        ∑ T ∈ residualDomSets G v, (T.card : ℚ) := by
  classical
  obtain ⟨hd,heq⟩ := dominating_family_partition G v
  rw [← heq,sum_union hd,omitted_card_sum G v hL]
  ring

/-- In a star-like graph, partial residual domination is already full residual domination. -/
theorem starLike_partial_full {G : SimpleGraph V} (v : V)
    (hL : (leafNeighbors G v).Nonempty) (hstar : StarLike G) :
    partialDomSets G v = residualDomSets G v := by
  classical
  apply subset_antisymm
  · intro T hT
    obtain ⟨hsub,hpartial⟩ := mem_partialDomSets.mp hT
    refine mem_residualDomSets.mpr ⟨hsub, ?_⟩
    intro x hx
    by_cases hvx : G.Adj v x
    · have hnotleaf : ¬ Leaf G x := fun hl => (mem_remaining.mp hx).2 ⟨hvx,hl⟩
      have hcount : 0 < leafCount G x := by
        rcases hstar x with hl | h1 | h2
        · exact False.elim (hnotleaf hl)
        · omega
        · omega
      obtain ⟨y,hy⟩ := card_pos.mp hcount
      obtain ⟨hxy,hly⟩ := mem_leafNeighbors.mp hy
      have hyv : y ≠ v := by
        rintro rfl
        obtain ⟨w,hw⟩ := hL
        obtain ⟨hvw,hlw⟩ := mem_leafNeighbors.mp hw
        have hxw : x = w := leaf_adj_unique hly hvw hvx
        exact hnotleaf (hxw ▸ hlw)
      have hvy : ¬ G.Adj v y := by
        intro hvy
        exact (mem_remaining.mp hx).1 (leaf_adj_unique hly hvy.symm hxy.symm)
      have hyR : y ∈ remaining G v := mem_remaining.mpr ⟨hyv,fun h => hvy h.1⟩
      have hdom := (leaf_dominated_iff hly hxy.symm T).mp (hpartial y hyR hvy)
      rcases hdom with hyT | hxT
      · exact Or.inr ⟨y,hyT,hxy⟩
      · exact Or.inl hxT
    · exact hpartial x hx hvx
  · exact residualDomSets_subset G v

/-- For one leaf and coincident residual families, a globally extremal mean forces the residual mean. -/
theorem residual_equality_from_global {G : SimpleGraph V} (v : V)
    (hl : leafCount G v = 1)
    (hfamilies : partialDomSets G v = residualDomSets G v)
    (hglobal : avd G = 2 * Fintype.card V / 3) :
    familyAverage (residualDomSets G v) = 2 * (remaining G v).card / 3 := by
  classical
  have hL : (leafNeighbors G v).Nonempty := card_pos.mp (by simpa [leafCount,hl] using
    (show 0 < leafCount G v by omega))
  have ha : (0 : ℚ) < (residualDomSets G v).card := by
    exact_mod_cast residualDomSets_card_pos G v
  have hs := stem_card_sum G v
  have htot := dominating_total_sum G v hL
  have hc := dominating_total_card G v hL
  have hn := remaining_card (G := G) v
  rw [hl,hfamilies] at hs hc
  norm_num at hs hc
  rw [hl] at htot hn
  norm_num at htot
  have hnq : ((remaining G v).card : ℚ) + 2 = Fintype.card V := by
    exact_mod_cast (by omega : (remaining G v).card + 2 = Fintype.card V)
  unfold avd familyAverage at hglobal
  rw [hc] at hglobal
  push_cast at hglobal
  have hg : (∑ S ∈ domSets G, (S.card : ℚ)) =
      (2 * Fintype.card V / 3) *
        (2 * (residualDomSets G v).card + (residualDomSets G v).card) :=
    (div_eq_iff (by positivity)).mp hglobal
  unfold familyAverage
  apply (div_eq_iff (ne_of_gt ha)).mpr
  nlinarith [congrArg (fun t : ℚ => t * (residualDomSets G v).card) hnq]

end D5.S3.Combinatorics.Graph.LocalDominatingStemBoundOmission
