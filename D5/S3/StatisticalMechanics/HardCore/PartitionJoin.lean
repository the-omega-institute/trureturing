/- GID: D5/S3/StatisticalMechanics/HardCore/PartitionJoin
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/PartitionJoin
   mirror-E: none(waiver:exact-symbolic-configuration-correspondence)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Sum]
   utility: none
   digest: A graph join confines every nonempty independent configuration to one side. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! Exact independent-configuration and partition identities for a graph join. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.StatisticalMechanics.HardCore.PartitionJoin

open Finset
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

attribute [local instance] Classical.propDecidable

variable {α β R : Type*} [DecidableEq α] [DecidableEq β]

/-- All cross edges are present; the induced graphs on the two sides are unchanged. -/
def join (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α ⊕ β) :=
  (Gᶜ ⊕g Hᶜ)ᶜ

private lemma join_left (G : SimpleGraph α) (H : SimpleGraph β) (u v : α) :
    (join G H).Adj (.inl u) (.inl v) ↔ G.Adj u v := by
  by_cases h : u = v
  · subst v; simp [join]
  · simp [join, SimpleGraph.compl_adj, h]

private lemma join_right (G : SimpleGraph α) (H : SimpleGraph β) (u v : β) :
    (join G H).Adj (.inr u) (.inr v) ↔ H.Adj u v := by
  by_cases h : u = v
  · subst v; simp [join]
  · simp [join, SimpleGraph.compl_adj, h]

/-- Equality of the complete independent-subset families. The two image families
intersect precisely at the empty subset. -/
theorem configurations_join (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (V : Finset α) (W : Finset β) :
    configurations (join G H) (V.disjSum W) =
      (configurations G V).image (fun S => S.map Function.Embedding.inl) ∪
      (configurations H W).image (fun T => T.map Function.Embedding.inr) := by
  classical
  ext S
  simp only [mem_union, mem_image]
  constructor
  · intro hS
    obtain ⟨hsub, hind⟩ := mem_filter.mp hS
    have hs := subset_disjSum.mp (mem_powerset.mp hsub)
    have hl : G.IsIndepSet (S.toLeft : Set α) := by
      intro x hx y hy hn he
      exact hind (by simpa using hx) (by simpa using hy)
        (by simpa using hn) ((join_left G H x y).mpr he)
    have hr : H.IsIndepSet (S.toRight : Set β) := by
      intro x hx y hy hn he
      exact hind (by simpa using hx) (by simpa using hy)
        (by simpa using hn) ((join_right G H x y).mpr he)
    by_cases hempty : S.toLeft = ∅
    · right
      refine ⟨S.toRight, mem_filter.mpr ⟨mem_powerset.mpr hs.2, hr⟩, ?_⟩
      have h := S.toLeft_disjSum_toRight
      simpa [hempty] using h
    · left
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hempty
      have hempty' : S.toRight = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hind (x := Sum.inl x) (y := Sum.inr y)
          (by simpa using hx) (by simpa using hy) (by simp)
          (by simp [join, SimpleGraph.compl_adj])
      refine ⟨S.toLeft, mem_filter.mpr ⟨mem_powerset.mpr hs.1, hl⟩, ?_⟩
      have h := S.toLeft_disjSum_toRight
      simpa [hempty'] using h
  · rintro (⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩)
    · obtain ⟨ht, hi⟩ := mem_filter.mp hT
      apply mem_filter.mpr
      constructor
      · apply mem_powerset.mpr
        simpa using (disjSum_mono (mem_powerset.mp ht) (empty_subset W))
      · intro x hx y hy hn he
        obtain ⟨a, ha, hea⟩ := mem_map.mp hx
        obtain ⟨b, hb, heb⟩ := mem_map.mp hy
        subst x; subst y
        exact hi ha hb (by simpa using hn) ((join_left G H a b).mp he)
    · obtain ⟨ht, hi⟩ := mem_filter.mp hT
      apply mem_filter.mpr
      constructor
      · apply mem_powerset.mpr
        simpa using (disjSum_mono (empty_subset V) (mem_powerset.mp ht))
      · intro x hx y hy hn he
        obtain ⟨a, ha, hea⟩ := mem_map.mp hx
        obtain ⟨b, hb, heb⟩ := mem_map.mp hy
        subst x; subst y
        exact hi ha hb (by simpa using hn) ((join_right G H a b).mp he)

theorem partition_join [CommRing R] (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (V : Finset α) (W : Finset β)
    (z : R) :
    partition (join G H) (V.disjSum W) (fun _ => z) =
      partition G V (fun _ => z) + partition H W (fun _ => z) - 1 := by
  classical
  let L := (configurations G V).image (fun S => S.map (Function.Embedding.inl : α ↪ α ⊕ β))
  let M := (configurations H W).image (fun T => T.map (Function.Embedding.inr : β ↪ α ⊕ β))
  have hempty (K : SimpleGraph α) [DecidableRel K.Adj] (U : Finset α) :
      (∅ : Finset α) ∈ configurations K U := by
    simp [configurations, SimpleGraph.IsIndepSet, Set.Pairwise]
  have hinter : L ∩ M = {∅} := by
    ext S
    simp only [mem_inter, mem_singleton]
    constructor
    · rintro ⟨hl, hr⟩
      obtain ⟨T, _, rfl⟩ := mem_image.mp hl
      obtain ⟨U, _, he⟩ := mem_image.mp hr
      have hh := congrArg Finset.toLeft he
      have hT : T = ∅ := by
        simpa only [← disjSum_empty, ← empty_disjSum, toLeft_disjSum] using hh.symm
      simp [hT]
    · rintro rfl
      constructor
      · exact mem_image.mpr ⟨∅, hempty G V, by simp⟩
      · exact mem_image.mpr ⟨∅, by simp [configurations, SimpleGraph.IsIndepSet, Set.Pairwise], by simp⟩
  have hL : (∑ S ∈ L, ∏ _ ∈ S, z) = partition G V (fun _ => z) := by
    dsimp [L]
    rw [Finset.sum_image (by intro S _ T _ h; exact Finset.map_injective _ h)]
    simp [partition]
  have hM : (∑ S ∈ M, ∏ _ ∈ S, z) = partition H W (fun _ => z) := by
    dsimp [M]
    rw [Finset.sum_image (by intro S _ T _ h; exact Finset.map_injective _ h)]
    simp [partition]
  have h := Finset.sum_union_inter (s₁ := L) (s₂ := M) (f := fun S => ∏ _ ∈ S, z)
  rw [hinter, sum_singleton, prod_empty, hL, hM] at h
  rw [partition, configurations_join]
  change (∑ S ∈ L ∪ M, ∏ _ ∈ S, z) = _
  linear_combination h

#print axioms configurations_join
#print axioms partition_join

end D5.S3.StatisticalMechanics.HardCore.PartitionJoin
