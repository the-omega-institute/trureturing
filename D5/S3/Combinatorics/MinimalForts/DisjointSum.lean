/- GID: D5/S3/Combinatorics/MinimalForts/DisjointSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/DisjointSum
   mirror-E: none(waiver:structural-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Sum]
   utility: none
   digest: Minimal forts of a disjoint union occupy exactly one component. -/

import D5.S3.Combinatorics.MinimalForts.UniversalRoot
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Sum

/-! Disjoint components do not contribute selected neighbors to each other. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.DisjointSum

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open D5.S3.Combinatorics.MinimalForts.UniversalRoot

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance sumDecidable : DecidableRel (G ⊕g H).Adj := by
  intro v w
  cases v <;> cases w <;> dsimp [SimpleGraph.sum] <;> infer_instance

private theorem mem_neighbors {A : Type*} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (v w : A) :
    w ∈ finiteNeighbors J v ↔ J.Adj v w :=
  Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and])

private theorem neighbors_left (S : Finset V) (T : Finset W) (v : V) :
    finiteNeighbors (G ⊕g H) (.inl v) ∩ S.disjSum T =
      (finiteNeighbors G v ∩ S).disjSum ∅ := by
  ext w
  cases w <;> simp only [Finset.mem_inter, mem_neighbors, Finset.inl_mem_disjSum,
    Finset.inr_mem_disjSum, Finset.notMem_empty, and_false, SimpleGraph.sum_adj_inl,
    SimpleGraph.sum_adj, false_and]

private theorem neighbors_right (S : Finset V) (T : Finset W) (v : W) :
    finiteNeighbors (G ⊕g H) (.inr v) ∩ S.disjSum T =
      (∅ : Finset V).disjSum (finiteNeighbors H v ∩ T) := by
  ext w
  cases w <;> simp only [Finset.mem_inter, mem_neighbors, Finset.inl_mem_disjSum,
    Finset.inr_mem_disjSum, Finset.notMem_empty, and_false, SimpleGraph.sum_adj_inr,
    SimpleGraph.sum_adj, false_and]

theorem fort_sum_iff (S : Finset V) (T : Finset W) :
    IsFort (G ⊕g H) (S.disjSum T) ↔
      (S.Nonempty ∨ T.Nonempty) ∧
      (∀ v ∉ S, (finiteNeighbors G v ∩ S).card ≠ 1) ∧
      (∀ w ∉ T, (finiteNeighbors H w ∩ T).card ≠ 1) := by
  constructor
  · rintro ⟨hne, hf⟩
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := hne
      cases v with
      | inl v => exact Or.inl ⟨v, by simpa using hv⟩
      | inr v => exact Or.inr ⟨v, by simpa using hv⟩
    · intro v hv
      have h := hf (.inl v) (by simpa using hv)
      simpa only [neighbors_left, Finset.card_disjSum, Finset.card_empty, add_zero] using h
    · intro v hv
      have h := hf (.inr v) (by simpa using hv)
      simpa only [neighbors_right, Finset.card_disjSum, Finset.card_empty, zero_add] using h
  · rintro ⟨hne, hl, hr⟩
    refine ⟨?_, ?_⟩
    · rcases hne with ⟨v, hv⟩ | ⟨v, hv⟩
      · exact ⟨.inl v, by simpa using hv⟩
      · exact ⟨.inr v, by simpa using hv⟩
    · intro v hv
      cases v with
      | inl v =>
        simpa only [neighbors_left, Finset.card_disjSum, Finset.card_empty, add_zero] using
          hl v (by simpa using hv)
      | inr v =>
        simpa only [neighbors_right, Finset.card_disjSum, Finset.card_empty, zero_add] using
          hr v (by simpa using hv)

private theorem left_fort (S : Finset V) (hf : IsFort G S) :
    IsFort (G ⊕g H) (S.disjSum (∅ : Finset W)) :=
  (fort_sum_iff G H _ _).mpr ⟨Or.inl hf.1, hf.2, by simp⟩

private theorem right_fort (T : Finset W) (hf : IsFort H T) :
    IsFort (G ⊕g H) ((∅ : Finset V).disjSum T) :=
  (fort_sum_iff G H _ _).mpr ⟨Or.inr hf.1, by simp, hf.2⟩

/-- This classification is exhaustive over all subsets of the actual disjoint graph. -/
theorem minimalFort_disjSum_iff (S : Finset V) (T : Finset W) :
    MinimalFort (G ⊕g H) (S.disjSum T) ↔
      (MinimalFort G S ∧ T = ∅) ∨ (S = ∅ ∧ MinimalFort H T) := by
  constructor
  · rintro ⟨hf, hm⟩
    have hs := (fort_sum_iff G H S T).mp hf
    rcases hs.1 with hS | hT
    · have hfS : IsFort G S := ⟨hS, hs.2.1⟩
      have hcontain := hm (S.disjSum ∅)
        (Finset.disjSum_mono (Finset.Subset.refl S) (Finset.empty_subset T))
        (left_fort G H S hfS)
      have ht0 : T = ∅ := by
        have h := (Finset.subset_disjSum.mp hcontain).2
        simpa using h
      refine Or.inl ⟨⟨hfS, ?_⟩, ht0⟩
      intro U hUS hU
      have hcontain := hm (U.disjSum ∅)
        (Finset.disjSum_mono hUS (Finset.empty_subset T)) (left_fort G H U hU)
      have h := (Finset.subset_disjSum.mp hcontain).1
      simpa using h
    · have hfT : IsFort H T := ⟨hT, hs.2.2⟩
      have hcontain := hm ((∅ : Finset V).disjSum T)
        (Finset.disjSum_mono (Finset.empty_subset S) (Finset.Subset.refl T))
        (right_fort G H T hfT)
      have hs0 : S = ∅ := by
        have h := (Finset.subset_disjSum.mp hcontain).1
        simpa using h
      refine Or.inr ⟨hs0, ⟨hfT, ?_⟩⟩
      intro U hUT hU
      have hcontain := hm ((∅ : Finset V).disjSum U)
        (Finset.disjSum_mono (Finset.empty_subset S) hUT) (right_fort G H U hU)
      have h := (Finset.subset_disjSum.mp hcontain).2
      simpa using h
  · rintro (⟨⟨hS, hmS⟩, rfl⟩ | ⟨rfl, ⟨hT, hmT⟩⟩)
    · refine ⟨left_fort G H S hS, ?_⟩
      intro F hF hf
      have hparts := Finset.subset_disjSum.mp hF
      have hr : F.toRight = ∅ := by simpa using hparts.2
      have hff : IsFort (G ⊕g H) (F.toLeft.disjSum ∅) := by
        simpa only [← hr, Finset.toLeft_disjSum_toRight] using hf
      have hfparts := (fort_sum_iff G H _ _).mp hff
      have hbase : IsFort G F.toLeft :=
        ⟨hfparts.1.resolve_right (by simp), hfparts.2.1⟩
      have hmin := hmS F.toLeft hparts.1 hbase
      apply Finset.disjSum_subset.mpr
      exact ⟨hmin, Finset.empty_subset _⟩
    · refine ⟨right_fort G H T hT, ?_⟩
      intro F hF hf
      have hparts := Finset.subset_disjSum.mp hF
      have hl : F.toLeft = ∅ := by simpa using hparts.1
      have hff : IsFort (G ⊕g H) ((∅ : Finset V).disjSum F.toRight) := by
        simpa only [← hl, Finset.toLeft_disjSum_toRight] using hf
      have hfparts := (fort_sum_iff G H _ _).mp hff
      have hbase : IsFort H F.toRight :=
        ⟨hfparts.1.resolve_left (by simp), hfparts.2.2⟩
      have hmin := hmT F.toRight hparts.2 hbase
      apply Finset.disjSum_subset.mpr
      exact ⟨Finset.empty_subset _, hmin⟩

/-- Counts add because the two full classes live on disjoint nonempty supports. -/
theorem minimalFort_sum_count :
    (minimalForts (G ⊕g H)).card = (minimalForts G).card + (minimalForts H).card := by
  classical
  let L : Finset V → Finset (V ⊕ W) := fun S => S.disjSum ∅
  let R : Finset W → Finset (V ⊕ W) := fun T => (∅ : Finset V).disjSum T
  have hLi : Function.Injective L := by
    intro S T h
    exact (Finset.disjSum_inj.mp h).1
  have hRi : Function.Injective R := by
    intro S T h
    exact (Finset.disjSum_inj.mp h).2
  have he : minimalForts (G ⊕g H) = (minimalForts G).image L ∪ (minimalForts H).image R := by
    ext F
    simp only [minimalForts, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image]
    constructor
    · intro hf
      have hc := (minimalFort_disjSum_iff G H F.toLeft F.toRight).mp
        (Finset.toLeft_disjSum_toRight.symm ▸ hf)
      rcases hc with ⟨hL, hR⟩ | ⟨hL, hR⟩
      · exact Or.inl ⟨F.toLeft, hL, by simpa only [L, ← hR] using F.toLeft_disjSum_toRight⟩
      · exact Or.inr ⟨F.toRight, hR, by simpa only [R, ← hL] using F.toLeft_disjSum_toRight⟩
    · rintro (⟨S, hS, rfl⟩ | ⟨T, hT, rfl⟩)
      · exact (minimalFort_disjSum_iff G H _ _).mpr (Or.inl ⟨hS, rfl⟩)
      · exact (minimalFort_disjSum_iff G H _ _).mpr (Or.inr ⟨rfl, hT⟩)
  have hd : Disjoint ((minimalForts G).image L) ((minimalForts H).image R) := by
    apply Finset.disjoint_left.mpr
    intro F hL hR
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨T, _, hT⟩ := Finset.mem_image.mp hR
    have hs0 : S = ∅ := (Finset.disjSum_inj.mp hT).1.symm
    have hnonempty := (Finset.mem_filter.mp hS).2.1.1
    simpa only [hs0, Finset.not_nonempty_empty] using hnonempty
  rw [he, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ hLi, Finset.card_image_of_injective _ hRi]

end D5.S3.Combinatorics.MinimalForts.DisjointSum
