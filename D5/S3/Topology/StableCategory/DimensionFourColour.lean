/- GID: D5/S3/Topology/StableCategory/DimensionFourColour
   generality: G
   mirror-B: none(waiver:support-for-the-four-piece-categorical-cover)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Top and mixed faces give two small-dimensional regions and preserve old labels on flags. -/

import D5.S3.Topology.OrdinaryCollarRetraction
import Mathlib.Order.Interval.Finset.Nat

/-! The mixed and pure faces yield two regions of dimension at most three. -/

set_option autoImplicit false

namespace D5.S3.Topology.StableCategory.DimensionFourColour

open BarycentricGraphDistance (Face)
open BarycentricBaseRigidity (sd)
open OrdinaryCollarRetraction (colourComplex)

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {X : Type} {K : PreAbstractSimplicialComplex X}

private def topOrMixed (label : X → Bool) (s : Face K) : Bool :=
  decide (s.val.card = 5 ∨ (s.val.image label).card = 2)

private theorem face_card_pos (s : Face K) : 0 < s.val.card :=
  (K.isRelLowerSet_faces s.property).1.card_pos

private theorem label_card_pos (label : X → Bool) (s : Face K) :
    0 < (s.val.image label).card :=
  ((K.isRelLowerSet_faces s.property).1.image label).card_pos

private theorem label_card_le_two (label : X → Bool) (s : Face K) :
    (s.val.image label).card ≤ 2 := by
  simpa using Finset.card_le_univ (s.val.image label)

private theorem flags_inj_on_size {s : Finset (Face K)} (hs : s ∈ sd K) :
    Set.InjOn (fun f : Face K => f.val.card) (s : Set (Face K)) := by
  intro a ha b hb he
  by_contra hne
  rcases hs.2.1 ha hb hne with h | h
  · exact (Finset.card_lt_card (show a.val ⊂ b.val from h)).ne he
  · exact (Finset.card_lt_card (show b.val ⊂ a.val from h)).ne he.symm

/-- Every face of an induced colour has at most four vertices. Equal-colour
comparable faces have the same set of original labels. -/
theorem two_low_dimensional_colours (label : X → Bool)
    (dimension : ∀ s ∈ K, s.card ≤ 5) :
    ∃ colour : Face K → Bool,
      (∀ s ∈ colourComplex (sd K) colour, s.card ≤ 4) ∧
      (∀ s ∈ colourComplex (sd K) (fun f => !colour f), s.card ≤ 4) ∧
      (∀ (a b : Face K), a ≤ b → colour a = colour b →
        a.val.image label = b.val.image label) := by
  let colour := topOrMixed (K := K) label
  have dim_le {s : Finset (Face K)} (hs : s ∈ sd K)
      (range : Finset ℕ) (bound : range.card = 4)
      (hsize : ∀ f ∈ s, f.val.card ∈ range) : s.card ≤ 4 := by
    rw [← Finset.card_image_of_injOn (flags_inj_on_size hs), ← bound]
    exact Finset.card_le_card (Finset.image_subset_iff.mpr hsize)
  refine ⟨colour, ?_, ?_, ?_⟩
  · intro s hs
    refine dim_le hs.1 (Finset.Icc 2 5) (by simp [Nat.card_Icc]) ?_
    intro f hf
    have h := of_decide_eq_true (hs.2 f hf)
    refine Finset.mem_Icc.mpr ⟨?_, dimension f.val f.property⟩
    rcases h with h | h
    · rw [h]
      exact Nat.le_add_right 2 3
    · exact h ▸ Finset.card_image_le
  · intro s hs
    refine dim_le hs.1 (Finset.Icc 1 4) (by simp [Nat.card_Icc]) ?_
    intro f hf
    have h : colour f = false := by
      have hnot := hs.2 f hf
      cases he : colour f <;> simp_all
    have hh := of_decide_eq_false h
    exact Finset.mem_Icc.mpr ⟨face_card_pos f,
      Nat.le_of_lt_succ (lt_of_le_of_ne (dimension f.val f.property)
        (fun he => hh (Or.inl he)))⟩
  · intro a b hab same
    by_cases he : a = b
    · simp only [he]
    have proper : a.val ⊂ b.val := show a < b from lt_of_le_of_ne hab he
    have hs := Finset.image_subset_image (f := label) (show a.val ⊆ b.val from hab)
    apply Finset.eq_of_subset_of_card_le hs
    have hap := label_card_pos label a
    have hbl := label_card_le_two label b
    have ha5 : a.val.card ≠ 5 := by
      intro h
      have hlt := Finset.card_lt_card proper
      exact (not_lt_of_ge (dimension b.val b.property)) (h ▸ hlt)
    by_cases hi : (b.val.image label).card ≤ (a.val.image label).card
    · exact hi
    have hlt := lt_of_not_ge hi
    have ha1 : (a.val.image label).card = 1 :=
      le_antisymm (Nat.le_of_lt_succ (hlt.trans_le hbl)) (Nat.succ_le_of_lt hap)
    rw [ha1] at hlt
    have hb2 : (b.val.image label).card = 2 := le_antisymm hbl (Nat.succ_le_of_lt hlt)
    have hca : colour a = false := by simp [colour, topOrMixed, ha5, ha1]
    have hcb : colour b = true := by simp [colour, topOrMixed, hb2]
    exact False.elim (Bool.false_ne_true (hca.symm.trans (same.trans hcb)))

end
end D5.S3.Topology.StableCategory.DimensionFourColour
