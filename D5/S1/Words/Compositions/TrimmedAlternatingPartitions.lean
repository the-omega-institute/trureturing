/- GID: D5/S1/Words/Compositions/TrimmedAlternatingPartitions
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/TrimmedAlternatingPartitions
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Trimmed alternating sums are distinct exactly for partitions with strict tails. -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Fintype.Card

/-!
# Trimmed alternating sums of partitions

The accumulator is an integer: natural subtraction would change the problem.
The initial accumulator is excluded from the output. Ordinary partition parts
are sorted decreasingly; only the tail is required to decrease strictly.
-/

namespace D5.S1.Words.Compositions.TrimmedAlternatingPartitions

/-- The recurrence `s_j = q_j - s_(j-1)`, excluding the initial value. -/
def sumsFrom (z : ℤ) : List ℕ → List ℤ
  | [] => []
  | a :: q => ((a : ℤ) - z) :: sumsFrom ((a : ℤ) - z) q

/-- Trimmed zero-based alternating partial sums, computed in the integers. -/
def trimmedSums (q : List ℕ) : List ℤ := sumsFrom 0 q

-- Two steps lower the nonpositive endpoint; the positive endpoint stays below B-z.
private theorem strict_bounds (q : List ℕ) (hs : q.Pairwise (· > ·))
    (hp : ∀ a ∈ q, 0 < a) (z B : ℤ) (hz : z ≤ 0)
    (hb : ∀ a ∈ q, (a : ℤ) < B) :
    ∀ x ∈ sumsFrom z q, x < z ∨ (0 < x ∧ x < B - z) := by
  induction q using List.twoStepInduction generalizing z B with
  | nil => simp [sumsFrom]
  | singleton a =>
    have ha := hp a (by simp)
    have haB := hb a (by simp)
    simp only [sumsFrom, List.mem_cons, List.not_mem_nil, or_false]
    intro x hx
    subst x
    right
    constructor <;> omega
  | cons_cons a b q ih =>
    have ha := hp a (by simp)
    have haB := hb a (by simp)
    have hab : b < a := (List.pairwise_cons.mp hs).1 b (by simp)
    have ht := ih hs.of_cons.of_cons (fun c hc => hp c (by simp [hc]))
      ((b : ℤ) - ((a : ℤ) - z)) (b : ℤ) (by omega)
      (fun c hc => by
        have := (List.pairwise_cons.mp hs.of_cons).1 c hc
        omega)
    simp only [sumsFrom, List.mem_cons]
    intro x hx
    rcases hx with rfl | rfl | hx
    · right; constructor <;> omega
    · left; omega
    · rcases ht x hx with h | ⟨hpos, hbound⟩
      · left; omega
      · right; constructor <;> omega

private theorem start_not_mem (q : List ℕ) (hs : q.Pairwise (· > ·))
    (hp : ∀ a ∈ q, 0 < a) (z : ℤ)
    (hz : z ≤ 0 ∨ ∀ a ∈ q, (a : ℤ) ≤ z) : z ∉ sumsFrom z q := by
  cases q with
  | nil => simp [sumsFrom]
  | cons a q =>
    have ha := hp a (by simp)
    rcases hz with hz | hz
    · have hb : ∀ c ∈ a :: q, (c : ℤ) < (a : ℤ) + 1 := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · have := (List.pairwise_cons.mp hs).1 c hc
          omega
      intro h
      rcases strict_bounds (a :: q) hs hp z ((a : ℤ) + 1) hz hb z h with h | h
      · omega
      · omega
    · have haz := hz a (by simp)
      simp only [sumsFrom, List.mem_cons, not_or]
      constructor
      · omega
      · intro h
        have ht := strict_bounds q hs.of_cons
          (fun c hc => hp c (by simp [hc])) ((a : ℤ) - z) a (by omega)
          (fun c hc => by
            have := (List.pairwise_cons.mp hs).1 c hc
            omega) z h
        rcases ht with ht | ht <;> omega

private theorem nodup_from_strict_tail (q : List ℕ) (hs : q.Pairwise (· ≥ ·))
    (hp : ∀ a ∈ q, 0 < a) (ht : q.tail.Pairwise (· > ·)) (z : ℤ)
    (hz : z ≤ 0 ∨ ∀ a ∈ q, (a : ℤ) ≤ z) : (sumsFrom z q).Nodup := by
  induction q generalizing z with
  | nil => simp [sumsFrom]
  | cons a q ih =>
    have hq : q.Pairwise (· > ·) := ht
    have hpq : ∀ b ∈ q, 0 < b := fun b hb => hp b (by simp [hb])
    have hz' : (a : ℤ) - z ≤ 0 ∨ ∀ b ∈ q, (b : ℤ) ≤ (a : ℤ) - z := by
      rcases hz with hz | hz
      · right
        intro b hb
        have := (List.pairwise_cons.mp hs).1 b hb
        omega
      · left
        have := hz a (by simp)
        omega
    exact List.nodup_cons.mpr ⟨start_not_mem q hq hpq _ hz',
      ih hs.of_cons hpq hq.tail _ hz'⟩

private theorem strict_tail_from_nodup (q : List ℕ) (hs : q.Pairwise (· ≥ ·))
    (z : ℤ) (hn : (sumsFrom z q).Nodup) : q.tail.Pairwise (· > ·) := by
  induction q generalizing z with
  | nil => simp
  | cons a q ih =>
    have hq := ih hs.of_cons ((a : ℤ) - z) hn.of_cons
    cases q with
    | nil => simp
    | cons b q =>
      cases q with
      | nil => simp
      | cons c q =>
        have hbc : c ≤ b := (List.pairwise_cons.mp hs.of_cons).1 c (by simp)
        have hne : b ≠ c := by
          intro he
          have hf := (List.nodup_cons.mp hn).1
          apply hf
          simp only [sumsFrom, List.mem_cons]
          right
          left
          omega
        change (b :: c :: q).Pairwise (· > ·)
        rw [List.pairwise_cons_cons_iff_of_trans]
        exact ⟨by omega, hq⟩

/-- Distinct trimmed alternating sums are equivalent to strict decrease of the tail. -/
theorem trimmedSums_nodup_iff_strict_tail (q : List ℕ)
    (hs : q.Pairwise (· ≥ ·)) (hp : ∀ a ∈ q, 0 < a) :
    (trimmedSums q).Nodup ↔ q.tail.Pairwise (· > ·) := by
  exact ⟨strict_tail_from_nodup q hs 0,
    fun ht => nodup_from_strict_tail q hs hp ht 0 (Or.inl le_rfl)⟩

-- Increase the largest part, with the empty partition sent to [1].
private def bump : List ℕ → List ℕ
  | [] => [1]
  | a :: q => (a + 1) :: q

private def unbump : List ℕ → List ℕ
  | [] => []
  | a :: q => if a = 1 then [] else (a - 1) :: q

private theorem bump_spec (q : List ℕ) (hs : q.Pairwise (· ≥ ·))
    (hp : ∀ a ∈ q, 0 < a) (ht : q.tail.Pairwise (· > ·)) :
    (bump q).Pairwise (· > ·) ∧ (∀ a ∈ bump q, 0 < a) ∧
      (bump q).sum = q.sum + 1 := by
  cases q with
  | nil => simp [bump]
  | cons a q =>
    refine ⟨List.pairwise_cons.mpr ⟨?_, ht⟩, ?_, ?_⟩
    · intro b hb
      have := (List.pairwise_cons.mp hs).1 b hb
      omega
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · exact hp b (by simp [hb])
    · simp [bump, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem unbump_bump (q : List ℕ) (hp : ∀ a ∈ q, 0 < a) :
    unbump (bump q) = q := by
  cases q with
  | nil => simp [bump, unbump]
  | cons a q =>
    have ha := hp a (by simp)
    simp [bump, unbump, Nat.ne_of_gt ha]

private theorem unbump_spec (q : List ℕ) (hne : q ≠ [])
    (hs : q.Pairwise (· > ·)) (hp : ∀ a ∈ q, 0 < a) :
    (unbump q).Pairwise (· ≥ ·) ∧ (∀ a ∈ unbump q, 0 < a) ∧
      (unbump q).tail.Pairwise (· > ·) ∧
      (unbump q).sum + 1 = q.sum ∧ bump (unbump q) = q := by
  cases q with
  | nil => exact False.elim (hne rfl)
  | cons a q =>
    have ha := hp a (by simp)
    by_cases ha1 : a = 1
    · subst a
      have hq : q = [] := by
        cases q with
        | nil => rfl
        | cons b q =>
          have hb := hp b (by simp)
          have hb1 := (List.pairwise_cons.mp hs).1 b (by simp)
          omega
      subst q
      simp [unbump, bump]
    · have ha2 : 1 < a := by omega
      simp only [unbump, if_neg ha1, List.tail_cons, List.sum_cons, bump]
      refine ⟨List.pairwise_cons.mpr ⟨?_, hs.of_cons.imp (fun h => Nat.le_of_lt h)⟩,
        ?_, hs.of_cons, ?_, ?_⟩
      · intro b hb
        have := (List.pairwise_cons.mp hs).1 b hb
        omega
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · exact hp b (by simp [hb])
      · omega
      · congr 1; omega

private theorem sorted_pos {n : ℕ} (p : Nat.Partition n) :
    ∀ a ∈ p.parts.sort (· ≥ ·), 0 < a := by
  intro a ha
  exact p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp ha)

private theorem sorted_sum {n : ℕ} (p : Nat.Partition n) :
    (p.parts.sort (· ≥ ·)).sum = n := by
  rw [← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]

private theorem sort_coe (q : List ℕ) (hs : q.Pairwise (· ≥ ·)) :
    (q : Multiset ℕ).sort (· ≥ ·) = q :=
  List.mergeSort_eq_self _ hs

private theorem sorted_strict {n : ℕ} (p : Nat.Partition n) (h : p.parts.Nodup) :
    (p.parts.sort (· ≥ ·)).Pairwise (· > ·) := by
  have hn : (p.parts.sort (· ≥ ·)).Nodup := by
    rw [← Multiset.coe_nodup, Multiset.sort_eq]
    exact h
  exact ((Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE.sortedGT_of_nodup hn).pairwise

private def raisePartition {n : ℕ}
    (p : {p : Nat.Partition n // (trimmedSums (p.parts.sort (· ≥ ·))).Nodup}) :
    {p : Nat.Partition (n + 1) // p.parts.Nodup} := by
  have ht := (trimmedSums_nodup_iff_strict_tail _
    (Multiset.pairwise_sort p.val.parts (· ≥ ·)) (sorted_pos p.val)).mp p.property
  have hb := bump_spec _ (Multiset.pairwise_sort p.val.parts (· ≥ ·)) (sorted_pos p.val) ht
  refine ⟨⟨bump (p.val.parts.sort (· ≥ ·)), ?_, ?_⟩, ?_⟩
  · intro a ha
    exact hb.2.1 a ha
  · simpa only [Multiset.sum_coe, sorted_sum] using hb.2.2
  · exact hb.1.sortedGT.nodup

private theorem raise_sorted {n : ℕ}
    (p : {p : Nat.Partition n // (trimmedSums (p.parts.sort (· ≥ ·))).Nodup}) :
    (raisePartition p).val.parts.sort (· ≥ ·) = bump (p.val.parts.sort (· ≥ ·)) := by
  apply sort_coe
  exact (bump_spec _ (Multiset.pairwise_sort p.val.parts (· ≥ ·)) (sorted_pos p.val)
    ((trimmedSums_nodup_iff_strict_tail _
      (Multiset.pairwise_sort p.val.parts (· ≥ ·)) (sorted_pos p.val)).mp p.property)).1.imp
        (fun h => Nat.le_of_lt h)

private theorem sorted_ne_nil {n : ℕ} (p : Nat.Partition (n + 1)) :
    p.parts.sort (· ≥ ·) ≠ [] := by
  intro h
  have := sorted_sum p
  rw [h] at this
  simp at this

private def lowerPartition {n : ℕ}
    (p : {p : Nat.Partition (n + 1) // p.parts.Nodup}) :
    {p : Nat.Partition n // (trimmedSums (p.parts.sort (· ≥ ·))).Nodup} := by
  have hu := unbump_spec _ (sorted_ne_nil p.val) (sorted_strict p.val p.property)
    (sorted_pos p.val)
  have hsum : (unbump (p.val.parts.sort (· ≥ ·))).sum = n := by
    have := hu.2.2.2.1
    rw [sorted_sum] at this
    omega
  refine ⟨⟨unbump (p.val.parts.sort (· ≥ ·)), ?_, ?_⟩, ?_⟩
  · intro a ha
    exact hu.2.1 a ha
  · exact hsum
  · change (trimmedSums ((unbump (p.val.parts.sort (· ≥ ·)) : Multiset ℕ).sort
      (· ≥ ·))).Nodup
    rw [sort_coe _ hu.1]
    exact (trimmedSums_nodup_iff_strict_tail _ hu.1 hu.2.1).mpr hu.2.2.1

private theorem lower_sorted {n : ℕ}
    (p : {p : Nat.Partition (n + 1) // p.parts.Nodup}) :
    (lowerPartition p).val.parts.sort (· ≥ ·) = unbump (p.val.parts.sort (· ≥ ·)) := by
  exact sort_coe _ (unbump_spec _ (sorted_ne_nil p.val)
    (sorted_strict p.val p.property) (sorted_pos p.val)).1

private def partitionEquiv (n : ℕ) :
    {p : Nat.Partition n // (trimmedSums (p.parts.sort (· ≥ ·))).Nodup} ≃
      {p : Nat.Partition (n + 1) // p.parts.Nodup} where
  toFun := raisePartition
  invFun := lowerPartition
  left_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    change (unbump ((raisePartition p).val.parts.sort (· ≥ ·)) : Multiset ℕ) = p.val.parts
    rw [raise_sorted, unbump_bump _ (sorted_pos p.val), Multiset.sort_eq]
  right_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    change (bump ((lowerPartition p).val.parts.sort (· ≥ ·)) : Multiset ℕ) = p.val.parts
    rw [lower_sorted,
      (unbump_spec _ (sorted_ne_nil p.val) (sorted_strict p.val p.property)
        (sorted_pos p.val)).2.2.2.2, Multiset.sort_eq]

open scoped Classical in
/-- Corrected A392698: the count at weight n is the distinct-part count at weight n+1. -/
theorem card_trimmedSums_eq_distincts (n : ℕ) :
    ((Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => (trimmedSums (p.parts.sort (· ≥ ·))).Nodup)).card =
    (Nat.Partition.distincts (n + 1)).card := by
  classical
  simpa only [Fintype.card_subtype, Nat.Partition.distincts] using
    Fintype.card_congr (partitionEquiv n)

#print axioms trimmedSums_nodup_iff_strict_tail
#print axioms card_trimmedSums_eq_distincts

end D5.S1.Words.Compositions.TrimmedAlternatingPartitions
