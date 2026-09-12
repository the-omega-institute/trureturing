/- GID: D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat, mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Tactic.Ring, mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: none
   digest: Label occurrences in restricted-growth words, counted by final block deficit. -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

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

private theorem maxLabel_le_length (n : ℕ) (w : List ℕ) (hw : w ∈ words n) :
    maxLabel w ≤ n := by
  induction n generalizing w with
  | zero =>
    simp [words] at hw
    simp [hw, maxLabel]
  | succ n ih =>
    cases w with
    | nil => simp [words] at hw
    | cons x v =>
      change x :: v ∈ (words n).biUnion (fun u =>
        (Finset.Icc 1 (maxLabel u + 1)).image fun y => y :: u) at hw
      obtain ⟨u, hv, hi⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hi
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      have hx := (Finset.mem_Icc.mp hy).2
      have hb := ih u hv
      change max y (maxLabel u) ≤ n + 1
      exact max_le (by omega) (by omega)

/-- A finite-fiber sum for the next RGF label, valid for arbitrary weights. -/
private theorem sum_words_succ (n : ℕ) (f : List ℕ → ℕ) :
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
private def topWord : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n + 1) :: topWord n

private theorem maxLabel_topWord (n : ℕ) : maxLabel (topWord n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change max (n + 1) (maxLabel (topWord n)) = n + 1
    simp [ih]

private theorem topWord_mem (n : ℕ) : topWord n ∈ words n := by
  induction n with
  | zero => simp [topWord, words]
  | succ n ih =>
    change (n + 1) :: topWord n ∈ (words n).biUnion (fun w =>
      (Finset.Icc 1 (maxLabel w + 1)).image fun x => x :: w)
    apply Finset.mem_biUnion.mpr
    refine ⟨topWord n, ih, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨n + 1, Finset.mem_Icc.mpr
      ⟨by omega, by simp [maxLabel_topWord]⟩, rfl⟩

/-- The maximum can attain the word length only along the all-new-label path. -/
private theorem eq_topWord_of_maxLabel_eq (n : ℕ) (w : List ℕ)
    (hw : w ∈ words n) (hm : maxLabel w = n) : w = topWord n := by
  induction n generalizing w with
  | zero =>
    simpa [topWord, words] using hw
  | succ n ih =>
    cases w with
    | nil => simp [words] at hw
    | cons x v =>
      change x :: v ∈ (words n).biUnion (fun u =>
        (Finset.Icc 1 (maxLabel u + 1)).image fun y => y :: u) at hw
      obtain ⟨u, hv, hi⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hi
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      have hx := (Finset.mem_Icc.mp hy).2
      have hb := maxLabel_le_length n u hv
      have hx' : y = n + 1 := by
        change max y (maxLabel u) = n + 1 at hm
        omega
      have hv' : maxLabel u = n := by omega
      simpa [topWord, hx'] using congrArg (List.cons (n + 1)) (ih u hv hv')

private theorem card_top_words (n : ℕ) :
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

private theorem nearFiberAny (n m : ℕ) (hn : 0 < n) :
    ((Finset.Icc 1 (m + 1)).filter fun x => max x m = n).card =
      if m = n then n else if m + 1 = n then 1 else 0 := by
  by_cases hm : m ≤ n
  · exact nearFiber n m hn hm
  · have heq : (Finset.Icc 1 (m + 1)).filter (fun x => max x m = n) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨_, hmax⟩
        have hle : m ≤ max x m := le_max_right x m
        omega
      · intro h
        simp at h
    rw [heq]
    simp [show m ≠ n by omega, show m + 1 ≠ n by omega]

private theorem card_max_step (N p : ℕ) (hp : 0 < p) :
    ((words (N + 1)).filter fun w => maxLabel w = p).card =
      p * ((words N).filter fun w => maxLabel w = p).card +
        ((words N).filter fun w => maxLabel w + 1 = p).card := by
  have heq : ((words N).filter (fun w => maxLabel w ≠ p)).filter
      (fun w => maxLabel w + 1 = p) =
      (words N).filter (fun w => maxLabel w + 1 = p) := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, _⟩, h⟩
      exact ⟨hw, h⟩
    · rintro ⟨hw, h⟩
      exact ⟨⟨hw, by omega⟩, h⟩
  calc
    _ = (words (N + 1)).sum (fun w => if maxLabel w = p then 1 else 0) :=
      Finset.card_filter _ _
    _ = (words N).sum (fun w =>
        (Finset.Icc 1 (maxLabel w + 1)).sum fun x =>
          if maxLabel (x :: w) = p then 1 else 0) := sum_words_succ N _
    _ = (words N).sum (fun w =>
        if maxLabel w = p then p else if maxLabel w + 1 = p then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro w _
      have hf := nearFiberAny p (maxLabel w) hp
      change (Finset.Icc 1 (maxLabel w + 1)).sum
        (fun x => if max x (maxLabel w) = p then 1 else 0) = _
      rw [← Finset.card_filter]
      exact hf
    _ = p * ((words N).filter fun w => maxLabel w = p).card +
        ((words N).filter fun w => maxLabel w + 1 = p).card := by
      simp [Finset.sum_ite, Finset.sum_const, heq, mul_comm]

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
private theorem card_near_words (n : ℕ) :
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

/-- A deficit of two consists of one triple block or two disjoint pairs.
The proof counts the corresponding RGFs through their maximum-label recurrence. -/
private theorem card_two_repeat_words (n : ℕ) :
    ((words (n + 2)).filter fun w => maxLabel w = n).card =
      (n + 2).choose 3 + 3 * (n + 2).choose 4 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hfilter : ((words (n + 2)).filter fun w => maxLabel w + 1 = n + 1) =
        ((words (n + 2)).filter fun w => maxLabel w = n) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, h⟩
        exact ⟨hw, by omega⟩
      · rintro ⟨hw, h⟩
        exact ⟨hw, by omega⟩
    have hp3 : (n + 3).choose 3 = (n + 2).choose 2 + (n + 2).choose 3 := by
      simpa only using Nat.choose_succ_succ' (n + 2) 2
    have hp4 : (n + 3).choose 4 = (n + 2).choose 3 + (n + 2).choose 4 := by
      simpa only using Nat.choose_succ_succ' (n + 2) 3
    have hfactor : 3 * (n + 2).choose 3 = n * (n + 2).choose 2 := by
      simpa only [show 2 + 1 = 3 by omega, show n + 2 - 2 = n by omega,
        mul_comm] using Nat.choose_succ_right_eq (n + 2) 2
    have hstep := card_max_step (n + 2) (n + 1) (by omega)
    rw [hfilter, card_near_words (n + 1), ih] at hstep
    calc
      ((words (n + 1 + 2)).filter fun w => maxLabel w = n + 1).card =
          (n + 1) * (n + 2).choose 2 +
            ((n + 2).choose 3 + 3 * (n + 2).choose 4) := by
        simpa only [show n + 1 + 2 = n + 3 by omega,
          show n + 2 + 1 = n + 3 by omega,
          show n + 1 + 1 = n + 2 by omega] using hstep
      _ = (n + 3).choose 3 + 3 * (n + 3).choose 4 := by
        rw [hp3, hp4]
        simp only [Nat.add_mul]
        omega

private theorem count_eq_zero_of_maxLabel_lt (w : List ℕ) (p : ℕ)
    (hp : maxLabel w < p) : w.count p = 0 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx : x ≠ p := by
      have hle : x ≤ maxLabel (x :: w) := by simp [maxLabel]
      omega
    have hw : maxLabel w < p := by
      have hle : maxLabel w ≤ maxLabel (x :: w) := by simp [maxLabel]
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

private theorem sum_count_fiber (w : List ℕ) (p : ℕ) (hp : 0 < p) :
    (Finset.Icc 1 (maxLabel w + 1)).sum (fun x => (x :: w).count p) =
      (maxLabel w + 1) * w.count p +
        (if p ≤ maxLabel w + 1 then 1 else 0) := by
  have hsum : (Finset.Icc 1 (maxLabel w + 1)).sum (fun x => (x :: w).count p) =
      (Finset.Icc 1 (maxLabel w + 1)).card * w.count p +
        (Finset.Icc 1 (maxLabel w + 1)).sum (fun x => if x = p then 1 else 0) := by
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib,
      Finset.sum_const, Nat.nsmul_eq_mul]
  rw [hsum]
  simp [Nat.card_Icc, Finset.mem_Icc, show 1 ≤ p from hp]

private theorem count_topWord_pred (k : ℕ) :
    (topWord (k + 2)).count (k + 1) = 1 := by
  have hne : k + 2 ≠ k + 1 := by omega
  have hzero := count_eq_zero_of_maxLabel_lt (topWord k) (k + 1)
    (by simp [maxLabel_topWord])
  simp [topWord, hzero]

private theorem secondLabelFiber (k : ℕ) (w : List ℕ)
    (hw : w ∈ words (k + 2)) :
    (Finset.Icc 1 (maxLabel w + 1)).sum (fun x => (x :: w).count (k + 1)) =
      (k + 2) * w.count (k + 1) +
        (if maxLabel w = k + 2 then 2 else 0) +
        (if maxLabel w = k + 1 then 1 else 0) +
        (if maxLabel w = k then 1 else 0) := by
  rw [sum_count_fiber w (k + 1) (by omega)]
  have hb := maxLabel_le_length (k + 2) w hw
  by_cases htop : maxLabel w = k + 2
  · have heq := eq_topWord_of_maxLabel_eq (k + 2) w hw htop
    have hc : w.count (k + 1) = 1 := by simpa [heq] using count_topWord_pred k
    simp [htop, hc]
  · by_cases hnear : maxLabel w = k + 1
    · simp [hnear]
    · by_cases hdouble : maxLabel w = k
      · have hc : w.count (k + 1) = 0 := count_eq_zero_of_maxLabel_lt w (k + 1)
          (by omega)
        simp [hdouble, hc]
      · have hsmall : maxLabel w < k := by omega
        have hc : w.count (k + 1) = 0 := count_eq_zero_of_maxLabel_lt w (k + 1)
          (by omega)
        simp [hc, htop, hnear, hdouble]
        omega

private theorem countFiber (n : ℕ) (hn : 0 < n) (w : List ℕ)
    (hw : w ∈ words n) :
    (Finset.Icc 1 (maxLabel w + 1)).sum (fun x => (x :: w).count n) =
      if maxLabel w = n then n + 2 else if maxLabel w + 1 = n then 1 else 0 := by
  have hsum : (Finset.Icc 1 (maxLabel w + 1)).sum (fun x => (x :: w).count n) =
      (Finset.Icc 1 (maxLabel w + 1)).card * w.count n +
        (Finset.Icc 1 (maxLabel w + 1)).sum (fun x => if x = n then 1 else 0) := by
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib,
      Finset.sum_const, Nat.nsmul_eq_mul]
  rw [hsum, count_top_of_mem n hn w hw]
  by_cases hm : maxLabel w = n
  · have h1 : 1 ≤ n := hn
    simp [hm, Finset.mem_Icc, Nat.card_Icc, h1]
  · by_cases hnear : maxLabel w + 1 = n
    · have hn0 : n ≠ 0 := by omega
      simp [hm, hnear, Finset.mem_Icc, Nat.card_Icc, hn0]
    · have hfar : maxLabel w + 1 < n := by
        have hb := maxLabel_le_length n w hw
        omega
      simp [hm, hnear, hfar, Finset.mem_Icc, Nat.card_Icc]

private theorem T_near_step (n : ℕ) (hn : 0 < n) :
    T (n + 1) n = n + 2 +
      ((words n).filter fun w => maxLabel w + 1 = n).card := by
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
  calc
    T (n + 1) n = (words n).sum (fun w =>
        (Finset.Icc 1 (maxLabel w + 1)).sum fun x => (x :: w).count n) := by
      rw [T, sum_words_succ]
    _ = (words n).sum (fun w =>
        if maxLabel w = n then n + 2 else if maxLabel w + 1 = n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact countFiber n hn w hw
    _ = n + 2 + ((words n).filter fun w => maxLabel w + 1 = n).card := by
      simp [Finset.sum_ite, card_top_words, heq]

private theorem T_second_step (k : ℕ) :
    T (k + 3) (k + 1) =
      2 + (k + 2) * T (k + 2) (k + 1) +
        (k + 2).choose 2 + (k + 2).choose 3 + 3 * (k + 2).choose 4 := by
  calc
    T (k + 3) (k + 1) = (words (k + 2)).sum (fun w =>
        (Finset.Icc 1 (maxLabel w + 1)).sum fun x => (x :: w).count (k + 1)) := by
      simpa only [show k + 3 = k + 2 + 1 by omega, T] using
        sum_words_succ (k + 2) (fun w => w.count (k + 1))
    _ = (words (k + 2)).sum (fun w =>
        (k + 2) * w.count (k + 1) +
          (if maxLabel w = k + 2 then 2 else 0) +
          (if maxLabel w = k + 1 then 1 else 0) +
          (if maxLabel w = k then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact secondLabelFiber k w hw
    _ = 2 + (k + 2) * T (k + 2) (k + 1) +
        (k + 2).choose 2 + (k + 2).choose 3 + 3 * (k + 2).choose 4 := by
      simp [T, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite,
        Finset.sum_const, card_top_words,
        card_near_words (k + 1), card_two_repeat_words k]
      simp only [show k + 1 + 1 = k + 2 by omega]
      omega

/-- Mathar's first OEIS A270236 conjecture, with the exact natural-number
division and the source's quantifier `n > 1`. -/
theorem mathar_f1 (n : ℕ) (hn : 1 < n) :
    T n (n - 1) = 2 + n * (n - 1) / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
  have hstep := T_near_step (k + 1) (by omega)
  have hfilter : ((words (k + 1)).filter (fun w => maxLabel w + 1 = k + 1)) =
      ((words (k + 1)).filter fun w => maxLabel w = k) := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨hw, by omega⟩
    · rintro ⟨hw, h⟩
      exact ⟨hw, by omega⟩
  have hchoose : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (k + 1) 1
  rw [show 2 + k = k + 2 by omega, show k + 2 - 1 = k + 1 by omega]
  calc
    T (k + 2) (k + 1) = 2 + (k + 2).choose 2 := by
      rw [hstep, hfilter, card_near_words k]
      omega
    _ = 2 + (k + 2) * (k + 1) / 2 := by
      rw [Nat.choose_two_right]
      congr 1

/-- Mathar's second OEIS A270236 conjecture, including the OEIS natural-number
quotient by `24`. -/
theorem mathar_f2 (n : ℕ) (hn : 1 < n) :
    T (n + 1) (n - 1) =
      2 + n * (n + 1) * (3 * n ^ 2 - 5 * n + 26) / 24 := by
  have hcomb : T (n + 1) (n - 1) =
      2 + n * T n (n - 1) + n.choose 2 + n.choose 3 + 3 * n.choose 4 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
    subst n
    simpa only [show 2 + k = k + 2 by omega,
      show k + 2 - 1 = k + 1 by omega,
      show k + 2 + 1 = k + 3 by omega] using T_second_step k
  have hc2 : 2 * n.choose 2 = n * (n - 1) := by
    simpa only [show 1 + 1 = 2 by omega, Nat.choose_one_right, mul_comm] using
      Nat.choose_succ_right_eq n 1
  have hc3 : 3 * n.choose 3 = n.choose 2 * (n - 2) := by
    simpa only [show 2 + 1 = 3 by omega, mul_comm] using
      Nat.choose_succ_right_eq n 2
  have hc4 : 4 * n.choose 4 = n.choose 3 * (n - 3) := by
    simpa only [show 3 + 1 = 4 by omega, mul_comm] using
      Nat.choose_succ_right_eq n 3
  have hs2 : 24 * n.choose 2 = 12 * n * (n - 1) := by
    calc
      24 * n.choose 2 = 12 * (2 * n.choose 2) := by ring
      _ = 12 * n * (n - 1) := by rw [hc2]; ring
  have hs3 : 24 * n.choose 3 = 4 * n * (n - 1) * (n - 2) := by
    calc
      24 * n.choose 3 = 8 * (3 * n.choose 3) := by ring
      _ = 8 * (n.choose 2 * (n - 2)) := by rw [hc3]
      _ = 4 * (2 * n.choose 2) * (n - 2) := by ring
      _ = 4 * n * (n - 1) * (n - 2) := by rw [hc2]; ring
  have hs4 : 24 * n.choose 4 = n * (n - 1) * (n - 2) * (n - 3) := by
    calc
      24 * n.choose 4 = 6 * (4 * n.choose 4) := by ring
      _ = 6 * (n.choose 3 * (n - 3)) := by rw [hc4]
      _ = 2 * (3 * n.choose 3) * (n - 3) := by ring
      _ = 2 * (n.choose 2 * (n - 2)) * (n - 3) := by rw [hc3]
      _ = (2 * n.choose 2) * (n - 2) * (n - 3) := by ring
      _ = n * (n - 1) * (n - 2) * (n - 3) := by rw [hc2]
  have hpoly :
      48 * n + 12 * (n + 1) * n * (n - 1) +
        4 * n * (n - 1) * (n - 2) +
        3 * n * (n - 1) * (n - 2) * (n - 3) =
      n * (n + 1) * (3 * n ^ 2 - 5 * n + 26) := by
    by_cases hsmall : n < 4
    · interval_cases n <;> norm_num at *
    · have hlarge : 4 ≤ n := by omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hlarge
      have hsub : 3 * (4 + j) ^ 2 - 5 * (4 + j) =
          3 * j ^ 2 + 19 * j + 28 := by
        have hright : 3 * (4 + j) ^ 2 =
            3 * j ^ 2 + 19 * j + 28 + 5 * (4 + j) := by ring
        omega
      rw [show 4 + j - 1 = j + 3 by omega,
        show 4 + j - 2 = j + 2 by omega,
        show 4 + j - 3 = j + 1 by omega, hsub]
      ring
  have hnum :
      24 * (n * (2 + n.choose 2) + n.choose 2 + n.choose 3 + 3 * n.choose 4) =
      n * (n + 1) * (3 * n ^ 2 - 5 * n + 26) := by
    calc
      _ = 48 * n + (n + 1) * (24 * n.choose 2) +
            24 * n.choose 3 + 3 * (24 * n.choose 4) := by ring
      _ = 48 * n + 12 * (n + 1) * n * (n - 1) +
            4 * n * (n - 1) * (n - 2) +
            3 * n * (n - 1) * (n - 2) * (n - 3) := by
        rw [hs2, hs3, hs4]
        ring
      _ = _ := hpoly
  have hf1 : T n (n - 1) = 2 + n.choose 2 := by
    simpa only [Nat.choose_two_right] using mathar_f1 n hn
  calc
    T (n + 1) (n - 1) =
        2 + (n * (2 + n.choose 2) + n.choose 2 + n.choose 3 + 3 * n.choose 4) := by
      rw [hcomb, hf1]
      omega
    _ = 2 + n * (n + 1) * (3 * n ^ 2 - 5 * n + 26) / 24 := by
      rw [← hnum]
      simp

#print axioms mathar_f1
#print axioms mathar_f2

end D5.S1.Recurrence.Invariants.RestrictedGrowthLabelOccurrences
