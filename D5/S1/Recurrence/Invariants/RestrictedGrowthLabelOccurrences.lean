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

theorem maxLabel_cons (w : List ℕ) (x : ℕ) :
    maxLabel (x :: w) = max x (maxLabel w) := rfl

theorem maxLabel_le_length (n : ℕ) (w : List ℕ) (hw : w ∈ words n) :
    maxLabel w ≤ n := by
  induction n generalizing w with
  | zero =>
    have heq := (mem_words_zero w).mp hw
    simp [heq, maxLabel]
  | succ n ih =>
    cases w with
    | nil => simp [words] at hw
    | cons x v =>
      obtain ⟨hv, _, hx⟩ := (mem_words_succ n v x).mp hw
      have hb := ih v hv
      rw [maxLabel_cons]
      exact max_le (by omega) (by omega)

/-- A finite-fiber sum for the next RGF label, valid for arbitrary weights. -/
theorem sum_words_succ (n : ℕ) (f : List ℕ → ℕ) :
    (words (n + 1)).sum f =
      (words n).sum (fun w => (Finset.Icc 1 (maxLabel w + 1)).sum fun x => f (x :: w)) := by
  have hdisj : (↑(words n) : Set (List ℕ)).PairwiseDisjoint
      (fun w => (Finset.Icc 1 (maxLabel w + 1)).image fun x => x :: w) := by
    intro w _ v _ hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hz'
    exact hne (List.cons.inj heq).2.symm
  rw [words, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_image]
  intro a _ b _ h
  exact (List.cons.inj h).1

end D5.S1.Recurrence.Invariants.RestrictedGrowthLabelOccurrences
