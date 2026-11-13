/- GID: D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites
   mirror-E: none(waiver:literal-catalan-pair-admissible-values)
   anchors: []
   utility: none
   digest: Half-open descent exclusions give the actual extensions of the Catalan pair. -/

import D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentSemantics

/-! Admissible values for the ordinary ascent sequences avoiding literal `10-1`
and `20-1`. The half-open interval includes the upper endpoint. These are the
objects in Ma--Zhang revision 3's Catalan bijection, not the other Catalan pair
`02-1,12-0`. The manuscript and Toufik Mansour's problem attribution are retained
in the owning Blueprint. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanSites

open OrdinaryAscentSemantics
open D5.S3.Combinatorics.Permutation.WordAscents (asc)

/-- Actual ordinary ascent words avoiding the indicated two literal patterns. -/
def CatalanWord (w : List ℕ) : Prop :=
  IsAscent w ∧ ¬ Contains .p101 w ∧ ¬ Contains .p201 w

/-- Values below the ascent bound, excluding each half-open descent interval `(b,a]`. -/
def sites (w : List ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (asc w + 2)).filter fun x =>
      ∀ i ∈ Finset.range (w.length - 1),
        ¬ (w.getD (i + 1) 0 < x ∧ x ≤ w.getD i 0)

theorem mem_sites (w : List ℕ) (x : ℕ) :
    x ∈ sites w ↔ x ≤ asc w + 1 ∧
      ∀ i, i + 1 < w.length → x ≤ w.getD (i + 1) 0 ∨ w.getD i 0 < x := by
  classical
  simp only [sites, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hx, hi⟩
    refine ⟨by omega, ?_⟩
    intro i hil
    have hb := hi i (by omega)
    omega
  · rintro ⟨hx, hi⟩
    refine ⟨by omega, ?_⟩
    intro i hil
    have hb := hi i (by omega)
    omega

theorem catalan_append_iff (w : List ℕ) (hne : w ≠ []) (x : ℕ) :
    CatalanWord (w ++ [x]) ↔ CatalanWord w ∧ x ∈ sites w := by
  simp only [CatalanWord, ascent_append_iff, if_neg hne,
    contains_append_iff, not_or, not_exists, not_and, mem_sites]
  constructor
  · rintro ⟨⟨ha, hx⟩, ⟨h101, hn101⟩, h201, hn201⟩
    refine ⟨⟨ha, h101, h201⟩, by omega, ?_⟩
    intro i hi
    have h1 := hn101 i hi
    have h2 := hn201 i hi
    simp only [Fits] at h1 h2
    omega
  · rintro ⟨⟨ha, h101, h201⟩, hx, hs⟩
    refine ⟨⟨ha, by omega⟩, ⟨h101, ?_⟩, h201, ?_⟩
    · intro i hi hf
      have hb := hs i hi
      simp only [Fits] at hf
      omega
    · intro i hi hf
      have hb := hs i hi
      simp only [Fits] at hf
      omega

theorem fresh_mem_sites (w : List ℕ) (ha : IsAscent w) : asc w + 1 ∈ sites w := by
  apply (mem_sites _ _).mpr
  refine ⟨le_refl _, ?_⟩
  intro i hi
  right
  have hb := entry_le_asc w ha i (by omega)
  omega

theorem last_mem_sites (w : List ℕ) (hw : CatalanWord w) (hne : w ≠ []) :
    w.getD (w.length - 1) 0 ∈ sites w := by
  have hp : 0 < w.length := List.length_pos_iff.mpr hne
  have hb := entry_le_asc w hw.1 (w.length - 1) (by omega)
  apply (mem_sites _ _).mpr
  refine ⟨by omega, ?_⟩
  intro i hi
  by_contra hn
  have hbad : w.getD (i + 1) 0 < w.getD (w.length - 1) 0 ∧
      w.getD (w.length - 1) 0 ≤ w.getD i 0 := by omega
  have higap : i + 1 < w.length - 1 := by
    by_contra hg
    have heq : i + 1 = w.length - 1 := by omega
    rw [heq] at hbad
    omega
  by_cases heq : w.getD i 0 = w.getD (w.length - 1) 0
  · exact hw.2.1 ⟨i, w.length - 1, higap, by omega, heq, by omega⟩
  · exact hw.2.2 ⟨i, w.length - 1, higap, by omega, hbad.1, by omega⟩

/-- The new adjacent pair is the only new interval in the site exclusions. -/
theorem mem_sites_append (w : List ℕ) (hne : w ≠ []) (x y : ℕ) :
    y ∈ sites (w ++ [x]) ↔ y ≤ asc (w ++ [x]) + 1 ∧
      (∀ i, i + 1 < w.length → y ≤ w.getD (i + 1) 0 ∨ w.getD i 0 < y) ∧
      (y ≤ x ∨ w.getD (w.length - 1) 0 < y) := by
  have hp : 0 < w.length := List.length_pos_iff.mpr hne
  rw [mem_sites]
  constructor
  · rintro ⟨hy, hs⟩
    refine ⟨hy, ?_, ?_⟩
    · intro i hi
      have hb := hs i (by simp; omega)
      rwa [List.getD_append _ _ _ _ (show i + 1 < w.length by omega),
        List.getD_append _ _ _ _ (show i < w.length by omega)] at hb
    · have hb := hs (w.length - 1) (by simp; omega)
      have heq : w.length - 1 + 1 = w.length := by omega
      rw [List.getD_append _ _ _ _ (show w.length - 1 < w.length by omega), heq] at hb
      simpa only [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self,
        List.getD_cons_zero] using hb
  · rintro ⟨hy, hs, hl⟩
    refine ⟨hy, ?_⟩
    intro i hi
    by_cases hil : i + 1 < w.length
    · rw [List.getD_append _ _ _ _ hil,
        List.getD_append _ _ _ _ (show i < w.length by omega)]
      exact hs i hil
    · have heq : i = w.length - 1 := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      subst i
      have heq : w.length - 1 + 1 = w.length := by omega
      rw [List.getD_append _ _ _ _ (show w.length - 1 < w.length by omega), heq]
      simpa only [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self,
        List.getD_cons_zero] using hl

end D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanSites
