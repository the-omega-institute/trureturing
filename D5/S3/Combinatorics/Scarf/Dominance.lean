/- GID: D5/S3/Combinatorics/Scarf/Dominance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Scarf/Dominance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: The collision pair and coordinate minima identify exactly the erasures preserving dominance. -/
/- proof_shape: isDominant_erase_iff_M_set_empty: content
   admission_basis: escape-witness
   escape_witness: The collision pair and coordinate minima identify exactly the erasures preserving dominance.
   Source: https://github.com/math-xmum/Brouwer/blob/f9dc162170e8711f78059a87edcd38ffc44a1bfb/Gametheory/Scarf.lean
   No mathematical novelty claim. -/
/-
MIT License

Copyright (c) 2025 Math_XMUM

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import Mathlib
import Mathlib.Analysis.Convex.StdSimplex
open Classical Finset
namespace D5.S3.Combinatorics.Scarf
variable {T : Type*} {I : Type*} [Inhabited T]
class IndexedLOrder (I T :Type*) where
  IST : I → LinearOrder T
variable [IST : IndexedLOrder I T]
set_option quotPrecheck false
local notation lhs "<[" i "]" rhs => (IST.IST i).lt lhs rhs
local notation lhs "≤[" i "]" rhs => (IST.IST i).le lhs rhs
namespace IndexedLOrder
variable (σ : Finset T) (C : Finset I)
def isDominant  :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ σ,  y ≤[i] x
abbrev isCell  := isDominant σ C
abbrev isRoom :=  isCell σ C ∧ C.card = σ.card
abbrev isDoor  :=  isCell σ C ∧ C.card = σ.card + 1
variable [DecidableEq T] [DecidableEq I]
inductive isDoorof (τ : Finset T) (D : Finset I) (σ : Finset T) (C : Finset I) : Prop
  | idoor (h0 : isCell σ C) (h1 : isDoor τ D) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (h0 : isCell σ C) (h1 : isDoor τ D) (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)
variable (τ : Finset T) (D : Finset I)
abbrev isOutsideDoor := IST.isDoor τ D ∧ τ = Finset.empty
abbrev isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty
def M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) : Set T :=
  {y : T | ∀ k ∈ D, k ≠ i → (@Finset.min' T (IST.IST k) τ h_nonempty) <[k] y}
def is_maximal_in_M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) (x : T) : Prop :=
  x ∈ M_set τ D i h_nonempty ∧ ∀ y ∈ M_set τ D i h_nonempty, y ≤[i] x
variable {σ C τ D}
lemma isDominant_erase_iff_M_set_empty [Fintype T] (τ : Finset T) (D : Finset I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) :
    ∀ i ∈ D, (IST.isDominant τ (D.erase i) ↔
      (∃ a b, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧
       @Finset.min' T (IST.IST a) τ h_nonempty =
         @Finset.min' T (IST.IST b) τ h_nonempty ∧
       (i = a ∨ i = b) ∧
       M_set τ D i h_nonempty = ∅)) := by
  classical
  let minAt {σ : Finset T} (h2 : σ.Nonempty) (i : I) : T :=
    @Finset.min' T (IST.IST i) σ h2
  have keylemma_of_dominant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) (h2: σ.Nonempty): σ  = C.image (minAt h2)  :=
    by
      ext a
      constructor
      · intro ha
        rw [mem_image]
        by_contra  hm
        push Not at hm
        obtain ⟨i,hi1,hi2⟩ := h1 a
        replace hm := hm i hi1
        dsimp [minAt] at hm
        have ha1 := @Finset.le_min' _ (IST.IST i) _ h2 a hi2
        have ha2 := @Finset.min'_le _ (IST.IST i) _ _ ha
        apply hm
        refine @eq_of_le_of_ge _ (IST.IST i).toPartialOrder _ _ ha2 ha1
      · suffices h: ∀ x ∈ C, minAt h2 x = a → a ∈ σ from
        by simp;exact h
        intro _ _ ha
        simp [minAt,<-ha,Finset.min'_mem]
  intro i hi
  constructor
  · intro h_dom
    have h_card : D.card = τ.card + 1 := h_door.2
    have h_image_card : D.card = (D.image (minAt h_nonempty)).card + 1 := by
      have h_dominant : IST.isDominant τ D := h_door.1
      have h_image_sub : D.image (minAt h_nonempty) ⊆ τ := by
        intro x hx
        simp at hx
        obtain ⟨j, _, hj_eq⟩ := hx
        rw [←hj_eq]
        dsimp [minAt]
        exact @Finset.min'_mem _ (IST.IST j) τ h_nonempty
      have h_image_eq : D.image (minAt h_nonempty) = τ := by
        convert (keylemma_of_dominant h_dominant h_nonempty).symm
      rw [h_card, h_image_eq]
    have h_collision : ∃ a b, a ∈ D ∧ b ∈ D ∧
        (minAt h_nonempty) a = (minAt h_nonempty) b ∧ a ≠ b ∧
        Set.InjOn (minAt h_nonempty) ((D : Set I) \ ({a, b} : Set I)) := by
      obtain ⟨t, hts, hinj, himage⟩ :=
        Finset.exists_subset_injOn_image_eq_of_surjOn (D : Set I) (D.image (minAt h_nonempty))
          (by intro y hy; exact Finset.mem_image.mp hy)
      have ht : t ⊆ D := hts
      have hcard : t.card = (D.image (minAt h_nonempty)).card := by
        rw [← himage, Finset.card_image_of_injOn hinj]
      have hdiff : (D \ t).card = 1 := by
        rw [Finset.card_sdiff_of_subset ht, h_image_card, ← hcard]
        omega
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hdiff
      have hbs : b ∈ D := (Finset.mem_sdiff.mp (hb.symm ▸ Finset.mem_singleton_self b)).1
      have hbnt : b ∉ t := (Finset.mem_sdiff.mp (hb.symm ▸ Finset.mem_singleton_self b)).2
      have hfb : minAt h_nonempty b ∈ t.image (minAt h_nonempty) := by
        rw [himage]
        exact Finset.mem_image.mpr ⟨b, hbs, rfl⟩
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hfb
      refine ⟨a, b, ht ha, hbs, hab, ?_, ?_⟩
      · intro heq
        exact hbnt (heq ▸ ha)
      · apply hinj.mono
        intro x hx
        rcases hx with ⟨hxs, hxab⟩
        have hxnb : x ≠ b := by
          intro hxb
          apply hxab
          simp [hxb]
        by_contra hxnt
        have hxb : x ∈ D \ t := Finset.mem_sdiff.mpr ⟨hxs, hxnt⟩
        rw [hb] at hxb
        exact hxnb (Finset.mem_singleton.mp hxb)
    obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, h_ne, _⟩ := h_collision
    use a, b, ha_mem, hb_mem, h_ne, h_eq_mini
    by_cases h_case : i = a ∨ i = b
    · constructor
      · exact h_case
      · ext y
        simp [M_set]
        obtain ⟨k, hk_in_erase, hk_dom⟩ := h_dom y
        have hk_in_D : k ∈ D := (Finset.mem_erase.mp hk_in_erase).2
        have hk_ne_i : k ≠ i := (Finset.mem_erase.mp hk_in_erase).1
        use k, hk_in_D, hk_ne_i
    · push Not at h_case
      obtain ⟨h_i_ne_a, h_i_ne_b⟩ := h_case
      have h_a_in_erase : a ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_a.symm, ha_mem⟩
      have h_b_in_erase : b ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_b.symm, hb_mem⟩
      have h_not_inj : ¬Set.InjOn (minAt h_nonempty) (D.erase i : Set I) := by
        intro h_inj
        exact h_ne (h_inj h_a_in_erase h_b_in_erase h_eq_mini)
      have h_image_lt : ((D.erase i).image (minAt h_nonempty)).card < (D.erase i).card := by
        by_contra h_not_lt
        push Not at h_not_lt
        have h_eq : ((D.erase i).image (minAt h_nonempty)).card = (D.erase i).card :=
          le_antisymm Finset.card_image_le h_not_lt
        have h_inj : Set.InjOn (minAt h_nonempty) (D.erase i : Set I) :=
          Finset.injOn_of_card_image_eq h_eq
        exact h_not_inj h_inj
      exfalso
      have h_dom_image := keylemma_of_dominant h_dom h_nonempty
      have h_tau_eq_image : τ.card = ((D.erase i).image (minAt h_nonempty)).card := by
        exact congrArg Finset.card h_dom_image
      have h_tau_eq_erase : τ.card = (D.erase i).card := by
        rw [Finset.card_erase_of_mem hi, h_door.2]; simp
      rw [h_tau_eq_erase] at h_tau_eq_image
      rw [h_tau_eq_image] at h_image_lt
      exact not_lt.mpr (le_refl _) h_image_lt
  · rintro ⟨a, b, ha_mem, hb_mem, h_ne, h_eq_mini, h_i_case, h_Mi_empty⟩
    intro y
    unfold M_set at h_Mi_empty
    simp only [Set.mem_ofPred_eq, Set.eq_empty_iff_forall_notMem] at h_Mi_empty
    specialize h_Mi_empty y
    push Not at h_Mi_empty
    obtain ⟨k, hk_mem, hk_ne_i, hk_not_lt⟩ := h_Mi_empty
    use k
    constructor
    · exact Finset.mem_erase.mpr ⟨hk_ne_i, hk_mem⟩
    · intro x hx
      let : LinearOrder T := IST.IST k
      have h_y_le_mini : y ≤[k] minAt h_nonempty k := hk_not_lt
      have h_mini_le_x : minAt h_nonempty k ≤[k] x := Finset.min'_le τ x hx
      exact @le_trans _ (IST.IST k).toPreorder _ _ _ h_y_le_mini h_mini_le_x
end IndexedLOrder
end D5.S3.Combinatorics.Scarf
