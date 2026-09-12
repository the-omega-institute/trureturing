/- GID: D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Order.Interval.Finset.Nat, Mathlib.Data.List.Count]
   utility: none
   digest: Label occurrences in restricted-growth words, counted by final block deficit. -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace D5.S1.Recurrence.Invariants.RestrictedGrowthLabelOccurrences

/-- Largest label in a word stored in reverse chronological order. -/
def maxLabel (w : List ℕ) : ℕ := w.foldr max 0

/-- Restricted-growth words of length `n`, in reverse chronological order.
The permitted next label is between `1` and one more than the previous maximum. -/
def words : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => (words n).biUnion fun w =>
      (Finset.Icc 1 (maxLabel w + 1)).image fun x => x :: w

/-- Sum of the occurrences of label `p` across all restricted-growth words. -/
def T (n p : ℕ) : ℕ := (words n).sum fun w => w.count p

theorem mem_words_zero (w : List ℕ) : w ∈ words 0 ↔ w = [] := by
  simp [words]

theorem mem_words_succ (n : ℕ) (w : List ℕ) (x : ℕ) :
    x :: w ∈ words (n + 1) ↔ w ∈ words n ∧ 1 ≤ x ∧ x ≤ maxLabel w + 1 := by
  simp only [words, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨v, hv, y, ⟨hlo, hhi⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    exact ⟨hv, hlo, hhi⟩
  · rintro ⟨hw, hlo, hhi⟩
    exact ⟨w, hw, x, ⟨hlo, hhi⟩, rfl⟩

end D5.S1.Recurrence.Invariants.RestrictedGrowthLabelOccurrences
