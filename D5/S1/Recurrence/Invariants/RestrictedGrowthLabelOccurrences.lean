/- GID: D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Order.Interval.Finset.Nat, Mathlib.Algebra.BigOperators.Group.Finset.Piecewise, Mathlib.Data.List.Count, Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: Label occurrences in restricted-growth words, counted by final block deficit. -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Choose.Basic

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

/-- The unique word which introduces a new label at every step. -/
def topWord : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n + 1) :: topWord n

theorem maxLabel_topWord (n : ℕ) : maxLabel (topWord n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [topWord, maxLabel_cons, ih]

theorem topWord_mem (n : ℕ) : topWord n ∈ words n := by
  induction n with
  | zero => simp [topWord, words]
  | succ n ih =>
    exact (mem_words_succ n (topWord n) (n + 1)).mpr
      ⟨ih, by omega, by simp [maxLabel_topWord]⟩

/-- The maximum can attain the word length only along the all-new-label path. -/
theorem eq_topWord_of_maxLabel_eq (n : ℕ) (w : List ℕ)
    (hw : w ∈ words n) (hm : maxLabel w = n) : w = topWord n := by
  induction n generalizing w with
  | zero =>
    simpa [topWord] using (mem_words_zero w).mp hw
  | succ n ih =>
    cases w with
    | nil => simp [words] at hw
    | cons x v =>
      obtain ⟨hv, _, hx⟩ := (mem_words_succ n v x).mp hw
      have hb := maxLabel_le_length n v hv
      have hx' : x = n + 1 := by
        rw [maxLabel_cons] at hm
        omega
      have hv' : maxLabel v = n := by omega
      simpa [topWord, hx'] using congrArg (List.cons (n + 1)) (ih v hv hv')

theorem card_top_words (n : ℕ) :
    ((words n).filter fun w => maxLabel w = n).card = 1 := by
  have heq : (words n).filter (fun w => maxLabel w = n) = {topWord n} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, hm⟩
      exact eq_topWord_of_maxLabel_eq n w hw hm
    · rintro rfl
      exact ⟨topWord_mem n, maxLabel_topWord n⟩
  simp [heq]

private theorem nearFiber (n m : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    ((Finset.Icc 1 (m + 1)).filter fun x => max x m = n).card =
      if m = n then n else if m + 1 = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst m
    have heq : (Finset.Icc 1 (n + 1)).filter (fun x => max x n = n) =
        Finset.Icc 1 n := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [heq, Nat.card_Icc]
    simp
  · by_cases hnext : m + 1 = n
    · have heq : (Finset.Icc 1 (m + 1)).filter (fun x => max x m = n) =
          {n} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        omega
      rw [heq]
      simp [hmn, hnext]
    · have heq : (Finset.Icc 1 (m + 1)).filter (fun x => max x m = n) =
          ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨_, hx⟩, hmax⟩
          have hbound : max x m ≤ m + 1 := max_le (by omega) (by omega)
          have hfalse : False := by omega
          exact hfalse.elim
        · intro h
          simp at h
      rw [heq]
      simp [hmn, hnext]

private theorem card_near_step (n : ℕ) (hn : 0 < n) :
    ((words (n + 1)).filter fun w => maxLabel w = n).card =
      n + ((words n).filter fun w => maxLabel w + 1 = n).card := by
  calc
    _ = (words (n + 1)).sum (fun w => if maxLabel w = n then 1 else 0) := by
      exact Finset.card_filter _ _
    _ = (words n).sum (fun w =>
        (Finset.Icc 1 (maxLabel w + 1)).sum fun x =>
          if maxLabel (x :: w) = n then 1 else 0) := sum_words_succ n _
    _ = (words n).sum (fun w =>
        if maxLabel w = n then n else if maxLabel w + 1 = n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hf := nearFiber n (maxLabel w) hn (maxLabel_le_length n w hw)
      change (Finset.Icc 1 (maxLabel w + 1)).sum
        (fun x => if max x (maxLabel w) = n then 1 else 0) = _
      rw [← Finset.card_filter]
      exact hf
    _ = n + ((words n).filter fun w => maxLabel w + 1 = n).card := by
      have heq : ((words n).filter (fun w => maxLabel w ≠ n)).filter
          (fun w => maxLabel w + 1 = n) =
          (words n).filter (fun w => maxLabel w + 1 = n) := by
        ext w
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hw, _⟩, hx⟩
          exact ⟨hw, hx⟩
        · rintro ⟨hw, hx⟩
          exact ⟨⟨hw, by omega⟩, hx⟩
      simp [Finset.sum_ite, card_top_words, heq]

/-- RGFs of length `n+1` with exactly one repetition are counted by a pair
of indices: the repetition time and its previously introduced label. -/
theorem card_near_words (n : ℕ) :
    ((words (n + 1)).filter fun w => maxLabel w = n).card = (n + 1).choose 2 := by
  induction n with
  | zero => simp [words, maxLabel]
  | succ n ih =>
    have hfilter : ((words (n + 1)).filter fun w => maxLabel w + 1 = n + 1) =
        ((words (n + 1)).filter fun w => maxLabel w = n) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, h⟩
        exact ⟨hw, by omega⟩
      · rintro ⟨hw, h⟩
        exact ⟨hw, by omega⟩
    rw [card_near_step (n + 1) (by omega), hfilter, ih]
    rw [Nat.choose_succ_succ' (n + 1) 1, Nat.choose_one_right]

private theorem count_eq_zero_of_maxLabel_lt (w : List ℕ) (p : ℕ)
    (hp : maxLabel w < p) : w.count p = 0 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx : x ≠ p := by
      have hle : x ≤ maxLabel (x :: w) := by simp [maxLabel_cons]
      omega
    have hw : maxLabel w < p := by
      have hle : maxLabel w ≤ maxLabel (x :: w) := by simp [maxLabel_cons]
      omega
    simp [hx, ih hw]

private theorem count_topWord_self (n : ℕ) :
    (topWord (n + 1)).count (n + 1) = 1 := by
  have hzero := count_eq_zero_of_maxLabel_lt (topWord n) (n + 1)
    (by simp [maxLabel_topWord])
  simp [topWord, hzero]

private theorem count_top_of_mem (n : ℕ) (hn : 0 < n) (w : List ℕ)
    (hw : w ∈ words n) : w.count n = if maxLabel w = n then 1 else 0 := by
  by_cases hm : maxLabel w = n
  · have heq := eq_topWord_of_maxLabel_eq n w hw hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [heq, maxLabel_topWord, count_topWord_self]
  · have hlt : maxLabel w < n := by
      have hb := maxLabel_le_length n w hw
      omega
    simp [hm, count_eq_zero_of_maxLabel_lt w n hlt]

end D5.S1.Recurrence.Invariants.RestrictedGrowthLabelOccurrences
