/- GID: D5/S3/Estimation/TimeArrow/RectangleHypergeometricKernel
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/RectangleHypergeometricKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform labelled four-cell tables have the exact hypergeometric intersection kernel. -/

import Mathlib

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
noncomputable section

/-- A fixed first margin, and a uniformly chosen second margin of size U.
The A cell is the intersection of the two labelled margins. -/
def intersectionEvent {α : Type*} [DecidableEq α] (V R : Finset α) (U t : ℕ) :
    Finset (Finset α) := (V.powersetCard U).filter fun B => (B ∩ R).card = t

/-- Split a table's second margin into its portions inside and outside the
first margin, retaining the original labels. -/
def intersectionSplit {α : Type*} [DecidableEq α] (V R : Finset α) (U t : ℕ)
    (hR : R ⊆ V) (ht : t ≤ U) :
    {B : Finset α // B ∈ intersectionEvent V R U t} ≃
      {A : Finset α // A ∈ R.powersetCard t} ×
      {D : Finset α // D ∈ (V \ R).powersetCard (U - t)} where
  toFun B := by
    have hB := mem_filter.mp B.property
    have hBV := (mem_powersetCard.mp hB.1).1
    have hBU := (mem_powersetCard.mp hB.1).2
    refine (⟨B.val ∩ R, mem_powersetCard.mpr ⟨inter_subset_right, hB.2⟩⟩,
      ⟨B.val \ R, mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff_left R hBV, ?_⟩⟩)
    rw [card_sdiff, hBU, inter_comm R, hB.2]
  invFun P := by
    have hA := mem_powersetCard.mp P.1.property
    have hD := mem_powersetCard.mp P.2.property
    have hd : Disjoint P.1.val P.2.val := disjoint_left.mpr fun x hxA hxD =>
      (mem_sdiff.mp (hD.1 hxD)).2 (hA.1 hxA)
    refine ⟨P.1.val ∪ P.2.val, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩⟩
    · exact union_subset (hA.1.trans hR) (hD.1.trans sdiff_subset)
    · rw [card_union_of_disjoint hd, hA.2, hD.2, Nat.add_sub_of_le ht]
    · have hi : (P.1.val ∪ P.2.val) ∩ R = P.1.val := by
        have hdR : Disjoint P.2.val R :=
          disjoint_of_subset_left hD.1 disjoint_sdiff_self_left
        rw [union_inter_distrib_right, Finset.inter_eq_left.mpr hA.1,
          disjoint_iff_inter_eq_empty.mp hdR, union_empty]
      rw [hi, hA.2]
  left_inv B := by
    apply Subtype.ext
    change (B.val ∩ R) ∪ (B.val \ R) = B.val
    rw [union_comm, sdiff_union_inter]
  right_inv P := by
    apply Prod.ext <;> apply Subtype.ext
    · ext x
      have hA := (mem_powersetCard.mp P.1.property).1
      have hD := (mem_powersetCard.mp P.2.property).1
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hx | hx, hr⟩
        · exact hx
        · exact False.elim ((mem_sdiff.mp (hD hx)).2 hr)
      · intro hx; exact ⟨Or.inl hx, hA hx⟩
    · ext x
      have hA := (mem_powersetCard.mp P.1.property).1
      have hD := (mem_powersetCard.mp P.2.property).1
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hx | hx, hr⟩
        · exact False.elim (hr (hA hx))
        · exact hx
      · intro hx; exact ⟨Or.inr hx, (mem_sdiff.mp (hD hx)).2⟩

/-- Exact counting law before normalization; the two margins refer to the
same labelled table. -/
theorem rectangle_intersection_card {α : Type*} [DecidableEq α]
    (V R : Finset α) (U t : ℕ) (hR : R ⊆ V) (ht : t ≤ U) :
    (intersectionEvent V R U t).card = R.card.choose t * (V.card - R.card).choose (U - t) := by
  have hc := Fintype.card_congr (intersectionSplit V R U t hR ht)
  simpa only [Fintype.card_coe, Fintype.card_prod, card_powersetCard,
    card_sdiff_of_subset hR] using hc

/-- The mass of the A-cell count, under the uniform second-margin law. -/
def rectangleMass {α : Type*} [DecidableEq α] (V R : Finset α) (U t : ℕ) : ℝ :=
  (intersectionEvent V R U t).card / (V.powersetCard U).card

/-- The exact hypergeometric formula for the finite labelled table law. -/
theorem rectangle_hypergeometric_mass {α : Type*} [DecidableEq α]
    (V R : Finset α) (U t : ℕ) (hR : R ⊆ V) (ht : t ≤ U) :
    rectangleMass V R U t =
      ((R.card.choose t : ℝ) * ((V.card - R.card).choose (U - t) : ℝ)) /
        (V.card.choose U : ℝ) := by
  simp only [rectangleMass, rectangle_intersection_card V R U t hR ht,
    card_powersetCard, Nat.cast_mul]

end
end D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
