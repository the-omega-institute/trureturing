/- GID: D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank
   mirror-E: none(waiver:actual-catalan-rank-succession)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Actual Catalan-pair prefixes have the Catalan rank succession rule. -/

import D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanSites
import Mathlib.Data.Finset.Sort

/-! The site shape is proved on actual avoiding words and retained at their
one-letter producers. It is not an assumed generating-tree predicate. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank

open OrdinaryAscentSemantics OrdinaryAscentCatalanSites
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation (asc)

/-- The last letter and the fresh bound are the two largest sites. -/
theorem sites_shape (w : List ℕ) (hw : CatalanWord w) (hne : w ≠ []) :
    ∀ y ∈ sites w, y ≤ w.getD (w.length - 1) 0 ∨ y = asc w + 1 := by
  induction w using List.reverseRecOn with
  | nil => contradiction
  | append_singleton w x ih =>
    by_cases he : w = []
    · subst w
      have hx := hw.1 0 (by simp)
      have hx0 : x = 0 := by simpa [IsAscent] using hx
      subst x
      intro y hy
      have hb := (mem_sites _ _).mp hy
      simp only [List.nil_append, asc, List.length_singleton, Nat.sub_self,
        Finset.range_zero, Finset.filter_empty, Finset.card_empty, zero_add,
        List.getD_cons_zero] at hb ⊢
      omega
    · obtain ⟨hp, hx⟩ := (catalan_append_iff w he x).mp hw
      have hlast : (w ++ [x]).getD ((w ++ [x]).length - 1) 0 = x := by simp
      intro y hy
      rw [hlast]
      have hd := (mem_sites_append w he x y).mp hy
      have hs := ih hp he x hx
      have hc := asc_append w x
      simp only [if_neg he] at hc
      by_cases hu : w.getD (w.length - 1) 0 < x
      · have hxv : x = asc w + 1 := by omega
        rw [if_pos hu] at hc
        omega
      · rw [if_neg hu, Nat.add_zero] at hc
        have hyold : y ∈ sites w := (mem_sites w y).mpr ⟨by omega, hd.2.1⟩
        have hys := ih hp he y hyold
        omega

/-- The complete site update, uniformly for descent, repetition, and fresh ascent. -/
theorem sites_append (w : List ℕ) (hw : CatalanWord w) (hne : w ≠ [])
    (x : ℕ) (hx : x ∈ sites w) :
    sites (w ++ [x]) = insert (asc (w ++ [x]) + 1) ((sites w).filter (· ≤ x)) := by
  have hcword := (catalan_append_iff w hne x).mpr ⟨hw, hx⟩
  have hc := asc_append w x
  simp only [if_neg hne] at hc
  have hxs := sites_shape w hw hne x hx
  ext y
  constructor
  · intro hy
    by_cases hf : y = asc (w ++ [x]) + 1
    · exact Finset.mem_insert.mpr (Or.inl hf)
    · have hd := (mem_sites_append w hne x y).mp hy
      have hyb : y ≤ asc (w ++ [x]) := by omega
      have hyold : y ∈ sites w := by
        apply (mem_sites _ _).mpr
        refine ⟨?_, hd.2.1⟩
        split_ifs at hc <;> omega
      have hys := sites_shape w hw hne y hyold
      have hyx : y ≤ x := by split_ifs at hc <;> omega
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hyold, hyx⟩))
  · intro hy
    rcases Finset.mem_insert.mp hy with hf | hy
    · rw [hf]
      exact fresh_mem_sites _ hcword.1
    · obtain ⟨hyold, hyx⟩ := Finset.mem_filter.mp hy
      have hd := (mem_sites w y).mp hyold
      apply (mem_sites_append w hne x y).mpr
      refine ⟨?_, hd.2, Or.inl hyx⟩
      split_ifs at hc <;> omega

/-- Zero-based rank among the actual admissible letters. -/
def rank (w : List ℕ) (x : ℕ) : ℕ := ((sites w).filter (· < x)).card

/-- Appending the letter of rank `i` produces exactly `i+2` sites. -/
theorem card_sites_append (w : List ℕ) (hw : CatalanWord w) (hne : w ≠ [])
    (x : ℕ) (hx : x ∈ sites w) :
    (sites (w ++ [x])).card = rank w x + 2 := by
  have hcword := (catalan_append_iff w hne x).mpr ⟨hw, hx⟩
  have hbound := entry_le_asc (w ++ [x]) hcword.1 w.length (by simp)
  simp only [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self,
    List.getD_cons_zero] at hbound
  have hnot : asc (w ++ [x]) + 1 ∉ (sites w).filter (· ≤ x) := by
    simp only [Finset.mem_filter]
    omega
  have hfilter : (sites w).filter (· ≤ x) = insert x ((sites w).filter (· < x)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hy, hyx⟩
      by_cases heq : y = x
      · exact Or.inl heq
      · exact Or.inr ⟨hy, by omega⟩
    · rintro (rfl | ⟨hy, hyx⟩)
      · exact ⟨hx, le_refl _⟩
      · exact ⟨hy, by omega⟩
  rw [sites_append w hw hne x hx, Finset.card_insert_of_notMem hnot, hfilter]
  have hself : x ∉ (sites w).filter (· < x) := by simp
  rw [Finset.card_insert_of_notMem hself]
  rfl

end D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank
