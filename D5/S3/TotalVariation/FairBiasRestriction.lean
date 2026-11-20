/- GID: D5/S3/TotalVariation/FairBiasRestriction
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasRestriction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The shelling partitions the augmented fair-bias faces into Boolean intervals. -/

import D5.S3.TotalVariation.FairBiasShelling
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Face enumeration by the first containing facet in the lexicographic shelling. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.FairBiasRestriction

open D5.S3.TotalVariation.FairBiasLink
open D5.S3.TotalVariation.FairBiasShelling

universe u v
variable {A : Type u} {L : Type v} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

/-- All nonempty facets of the signed complex. -/
noncomputable def facets (c : L → A) : Finset (Finset (L × Bool)) := by
  classical
  exact Finset.univ.filter (IsFacet c)

/-- The faces with the empty face adjoined. -/
noncomputable def augmentedFaces (c : L → A) : Finset (Finset (L × Bool)) := by
  classical
  exact insert ∅ (Finset.univ.filter (· ∈ signedComplex c))

theorem mem_facets {c : L → A} {B : Finset (L × Bool)} :
    B ∈ facets c ↔ IsFacet c B := by
  classical
  simp [facets]

private theorem mem_augmented {c : L → A} {S : Finset (L × Bool)} :
    S ∈ augmentedFaces c ↔ S = ∅ ∨ S ∈ signedComplex c := by
  classical
  simp [augmentedFaces]

/-- Vertices whose deletion leaves a subface contained in an earlier facet. -/
noncomputable def restrictionFace (c : L → A) (B : Finset (L × Bool)) :
    Finset (L × Bool) := by
  classical
  exact B.filter fun v => ∃ C ∈ facets c, lexBefore (L × Bool) C B ∧ B.erase v ⊆ C

/-- The facet B contains S and no strictly earlier facet contains S. -/
def FirstAt (c : L → A) (S B : Finset (L × Bool)) : Prop :=
  S ⊆ B ∧ ∀ C ∈ facets c, lexBefore (L × Bool) C B → ¬ S ⊆ C

/-- The faces first encountered at a facet form the interval from its restriction face. -/
theorem firstAt_iff_restriction_subset (c : L → A) {B S : Finset (L × Bool)}
    (hB : B ∈ facets c) (hS : S ⊆ B) :
    FirstAt c S B ↔ restrictionFace c B ⊆ S := by
  classical
  constructor
  · intro h v hv
    obtain ⟨_, C, hC, hCB, he⟩ := Finset.mem_filter.mp hv
    by_contra hnot
    exact h.2 C hC hCB (fun u hu => he (Finset.mem_erase.mpr
      ⟨fun h => hnot (h ▸ hu), hS hu⟩))
  · intro h
    refine ⟨hS, ?_⟩
    intro C hC hCB hSC
    obtain ⟨U, hU, hUB, hinter, v, hv⟩ :=
      lexicographic_facet_shelling c C B (mem_facets.mp hC) (mem_facets.mp hB) hCB
    have hvdiff : v ∈ (B : Set (L × Bool)) \ ↑U := by
      rw [hv]
      exact Set.mem_singleton v
    have herase : B.erase v ⊆ U := by
      intro u hu
      obtain ⟨hne, huB⟩ := Finset.mem_erase.mp hu
      by_contra huU
      have hx : u ∈ (B : Set (L × Bool)) \ ↑U := ⟨huB, huU⟩
      rw [hv] at hx
      exact hne (Set.mem_singleton_iff.mp hx)
    have hvR : v ∈ restrictionFace c B :=
      Finset.mem_filter.mpr ⟨hvdiff.1, U, mem_facets.mpr hU, hUB, herase⟩
    exact hvdiff.2 (hinter ⟨hSC (h hvR), hS (h hvR)⟩)

theorem exists_facet_superset (c : L → A) {S : Finset (L × Bool)}
    (hS : S ∈ signedComplex c) : ∃ B ∈ facets c, S ⊆ B := by
  classical
  let covers := (Finset.univ : Finset (Finset (L × Bool))).filter
    (fun B => B ∈ signedComplex c ∧ S ⊆ B)
  obtain ⟨B, hB, hmax⟩ := Finset.exists_maximal
    (s := covers) (⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS, Finset.Subset.refl _⟩⟩)
  obtain ⟨_, hface, hSB⟩ := Finset.mem_filter.mp hB
  refine ⟨B, mem_facets.mpr ⟨hface, ?_⟩, hSB⟩
  intro T hT hBT
  exact Finset.Subset.antisymm (hmax (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hT, hSB.trans hBT⟩) hBT) hBT

private theorem augmented_of_subset_facet (c : L → A) {B S : Finset (L × Bool)}
    (hB : B ∈ facets c) (hSB : S ⊆ B) : S ∈ augmentedFaces c := by
  classical
  by_cases he : S = ∅
  · exact mem_augmented.mpr (Or.inl he)
  · exact mem_augmented.mpr (Or.inr
      (((signedComplex c).isRelLowerSet_faces (mem_facets.mp hB).1).2 hSB
        (Finset.nonempty_iff_ne_empty.mpr he)))

private theorem exists_first_facet (c : L → A) (h : (facets c).Nonempty)
    {S : Finset (L × Bool)} (hS : S ∈ augmentedFaces c) :
    ∃ B ∈ facets c, FirstAt c S B := by
  classical
  let covers := (facets c).filter (S ⊆ ·)
  have hne : covers.Nonempty := by
    rcases mem_augmented.mp hS with rfl | hf
    · obtain ⟨B, hB⟩ := h
      exact ⟨B, Finset.mem_filter.mpr ⟨hB, Finset.empty_subset _⟩⟩
    · obtain ⟨B, hB, hSB⟩ := exists_facet_superset c hf
      exact ⟨B, Finset.mem_filter.mpr ⟨hB, hSB⟩⟩
  obtain ⟨B, hB, hmax⟩ := covers.exists_max_image
    (fun B => toColex (α := Finset (L × Bool)ᵒᵈ) B) hne
  obtain ⟨hBf, hSB⟩ := Finset.mem_filter.mp hB
  exact ⟨B, hBf, hSB, fun C hC hc hSC =>
    (not_lt_of_ge (hmax C (Finset.mem_filter.mpr ⟨hC, hSC⟩))) hc⟩

private theorem first_unique (c : L → A) {S B C : Finset (L × Bool)}
    (hB : B ∈ facets c) (hC : C ∈ facets c)
    (hb : FirstAt c S B) (hc : FirstAt c S C) : B = C := by
  rcases lt_trichotomy (toColex (α := Finset (L × Bool)ᵒᵈ) B)
      (toColex (α := Finset (L × Bool)ᵒᵈ) C) with h | h | h
  · exact (hb.2 C hC h hc.1).elim
  · exact toColex.injective h
  · exact (hc.2 B hB h hb.1).elim

private theorem sum_interval {V R : Type*} [DecidableEq V] [CommSemiring R]
    (U B : Finset V) (h : U ⊆ B) (t : R) :
    (∑ S ∈ Finset.Icc U B, t ^ S.card) = t ^ U.card * (1 + t) ^ (B.card - U.card) := by
  classical
  rw [Finset.Icc_eq_image_powerset h, Finset.sum_image]
  · have he (S : Finset V) (hS : S ∈ (B \ U).powerset) :
        (U ∪ S).card = U.card + S.card := by
      refine Finset.card_union_of_disjoint (Finset.disjoint_left.mpr ?_)
      intro v hv hvS
      exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hS hvS)).2 hv
    simp only [Finset.sum_congr rfl (fun S hS => congrArg (t ^ ·) (he S hS)), pow_add,
      ← Finset.mul_sum]
    congr 1
    rw [← Finset.card_sdiff_of_subset h]
    simpa [Finset.prod_const] using
      (Finset.prod_one_add (f := fun _ : V => t) (B \ U)).symm
  · intro S hS T hT he
    change U ∪ S = U ∪ T at he
    have hdisj {W : Finset V} (hW : W ∈ (B \ U).powerset) : Disjoint U W :=
      (disjoint_sdiff_self_left.mono_left (Finset.mem_powerset.mp hW)).symm
    simpa only [Finset.union_sdiff_cancel_left (hdisj hS),
      Finset.union_sdiff_cancel_left (hdisj hT)] using congrArg (· \ U) he

/-- The face enumerator evaluated at t, with the empty face contributing one. -/
noncomputable def faceEnumerator (c : L → A) {R : Type*} [CommSemiring R] (t : R) : R :=
  ∑ S ∈ augmentedFaces c, t ^ S.card

private theorem faceEnumerator_of_facets (c : L → A) {R : Type*} [CommSemiring R] (t : R)
    (h : (facets c).Nonempty) :
    let d := Fintype.card L - Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range c))
    faceEnumerator c t =
      ∑ B ∈ facets c, t ^ (restrictionFace c B).card *
        (1 + t) ^ (d - (restrictionFace c B).card) := by
  classical
  let d := Fintype.card L - Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) (Set.range c))
  let blocks (B : Finset (L × Bool)) := Finset.Icc (restrictionFace c B) B
  have hpartition : (facets c).biUnion blocks = augmentedFaces c := by
    ext S
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨B, hB, hmem⟩
      exact augmented_of_subset_facet c hB (Finset.mem_Icc.mp hmem).2
    · intro hS
      obtain ⟨B, hB, hb⟩ := exists_first_facet c h hS
      exact ⟨B, hB, Finset.mem_Icc.mpr
        ⟨(firstAt_iff_restriction_subset c hB hb.1).mp hb, hb.1⟩⟩
  have hd : (↑(facets c) : Set (Finset (L × Bool))).PairwiseDisjoint blocks := by
    intro B hB C hC hne
    apply Finset.disjoint_left.mpr
    intro S hs ht
    obtain ⟨hRS, hSB⟩ := Finset.mem_Icc.mp hs
    obtain ⟨hRT, hSC⟩ := Finset.mem_Icc.mp ht
    exact hne (first_unique c hB hC
      ((firstAt_iff_restriction_subset c hB hSB).mpr hRS)
      ((firstAt_iff_restriction_subset c hC hSC).mpr hRT))
  unfold faceEnumerator
  rw [← hpartition, Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro B hB
  have hsum := sum_interval (restrictionFace c B) B (Finset.filter_subset _ _) t
  rwa [show B.card = d from facet_card_eq_nullity c B (mem_facets.mp hB)] at hsum

private theorem faceEnumerator_eq_one (c : L → A) {R : Type*} [CommSemiring R] (t : R)
    (h : facets c = ∅) : faceEnumerator c t = 1 := by
  classical
  have he : augmentedFaces c = {∅} := by
    ext S
    rw [mem_augmented, Finset.mem_singleton]
    exact ⟨fun hs => hs.elim id (fun hf => by
      obtain ⟨B, hB, _⟩ := exists_facet_superset c hf
      simp [h] at hB), Or.inl⟩
  simp [faceEnumerator, he]

open Classical in
/-- Each nonempty facet contributes its interval. With no nonempty facets, only the empty face
contributes. -/
theorem faceEnumerator_eq_sum (c : L → A) {R : Type*} [CommSemiring R] (t : R) :
    let d := Fintype.card L - Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range c))
    faceEnumerator c t =
      if (facets c).Nonempty then
        ∑ B ∈ facets c, t ^ (restrictionFace c B).card *
          (1 + t) ^ (d - (restrictionFace c B).card)
      else 1 := by
  dsimp only
  split_ifs with h
  · exact faceEnumerator_of_facets c t h
  · exact faceEnumerator_eq_one c t (Finset.not_nonempty_iff_eq_empty.mp h)

end D5.S3.TotalVariation.FairBiasRestriction
