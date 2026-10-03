/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentGrowth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentGrowth
   mirror-E: none(waiver:weak-ascent-growth)
   anchors: [mathlib/module/Mathlib.Data.List.MinMax]
   utility: none
   digest: The height bound for growing weak ascent sequences. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentDefs
import Mathlib.Data.List.MinMax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentGrowth

open WeakAscentDefs

theorem height_dominates (e : List ℕ) (he : IsWeakAscent e) :
    e.foldr max 0 < 1 + wasc e := by
  have append_ascents (parent : List ℕ) (letter : ℕ) :
      wasc (parent ++ [letter]) = wasc parent +
        if parent = [] then 0 else if parent.getLast?.getD 0 ≤ letter then 1 else 0 := by
    induction parent with
    | nil => simp [wasc]
    | cons first rest ih =>
      cases rest with
      | nil =>
        by_cases hpair : first ≤ letter <;> simp [wasc, hpair]
      | cons second tail =>
        simp only [List.cons_append, wasc, List.tail_cons, List.zip_cons_cons,
          List.filter_cons] at ih ⊢
        by_cases hpair : first ≤ second
        · simp [hpair, List.getLast?_cons_cons, List.cons_ne_nil] at ih ⊢
          omega
        · simp only [decide_eq_true_eq, hpair, reduceCtorEq, ↓reduceIte,
            List.getLast?_cons_cons] at ih ⊢
          exact ih
  have max_append (parent : List ℕ) (letter : ℕ) :
      (parent ++ [letter]).foldr max 0 = max (parent.foldr max 0) letter := by
    induction parent with
    | nil => simp
    | cons first rest ih => simp [ih, max_assoc]
  induction e using List.reverseRecOn with
  | nil => simp [wasc]
  | append_singleton parent letter ih =>
    have hprefix : IsWeakAscent parent := by
      intro index hindex
      have hbound := he index (by simp; omega)
      rw [List.getD_append _ _ _ _ hindex,
        List.take_append_of_le_length (Nat.le_of_lt hindex)] at hbound
      exact hbound
    have hletter := he parent.length (by simp)
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)] at hletter
    simp only [Nat.sub_self, List.getD_cons_zero] at hletter
    rw [max_append, append_ascents]
    by_cases hempty : parent = []
    · subst parent
      simp [wasc] at hletter ⊢
      omega
    · have hparent := ih hprefix
      simp only [if_neg hempty]
      have hlength : parent.length ≠ 0 := by simpa using hempty
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hletter
      simp only [if_neg hlength] at hletter
      have hlast : parent.getLast?.getD 0 ≤ parent.foldr max 0 := by
        have hmem := List.getLast_mem hempty
        have heq : parent.getLast?.getD 0 = parent.getLast hempty := by
          simp [List.getLast?_eq_some_getLast hempty]
        rw [heq]
        exact List.le_max_of_le hmem (Nat.le_refl _)
      by_cases hascent : parent.getLast?.getD 0 ≤ letter
      · simp only [if_pos hascent]
        omega
      · simp only [if_neg hascent]
        omega

end D5.S3.Combinatorics.WeakAscent.WeakAscentGrowth
