/- GID: D5/S1/Words/ZeckendorfOrder
   generality: I
   mirror-B: D5/B/S1/Words/ZeckendorfOrder
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: Zeckendorf lists ordered from greatest index down have numerical lexicographic order. -/

import Mathlib.Data.Nat.Fib.Zeckendorf

/- Provenance: Native proof over pinned mathlib. -/

namespace D5.S1.Words

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem head_ge_two {a : ℕ} {l : List ℕ}
    (h : (a :: l).IsZeckendorfRep) : 2 ≤ a := by
  rw [List.IsZeckendorfRep, List.cons_append,
    List.isChain_iff_pairwise, List.pairwise_cons] at h
  exact h.1 0 (by simp)

private theorem tail_isZeckendorfRep {a : ℕ} {l : List ℕ}
    (h : (a :: l).IsZeckendorfRep) : l.IsZeckendorfRep := by
  rw [List.IsZeckendorfRep, List.cons_append,
    List.isChain_iff_pairwise, List.pairwise_cons] at h
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise]
  exact h.2

private theorem sum_fib_lt_of_lex {l k : List ℕ}
    (hl : l.IsZeckendorfRep) (hk : k.IsZeckendorfRep)
    (hlex : List.Lex (· < ·) l k) :
    (l.map Nat.fib).sum < (k.map Nat.fib).sum := by
  induction hlex with
  | nil =>
      simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons]
      exact lt_of_lt_of_le
        (Nat.fib_pos.2 (Nat.zero_lt_two.trans_le (head_ge_two hk)))
        (Nat.le_add_right _ _)
  | @rel a b l k hab =>
      exact lt_of_lt_of_le (hl.sum_fib_lt (by simpa using hab)) (by simp)
  | @cons a l k hlex ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_lt_add_left
        (ih (tail_isZeckendorfRep hl) (tail_isZeckendorfRep hk)) _

/-- On canonical Fibonacci-index lists, lexicographic order is the order of their
Fibonacci sums. The list heads are the greatest occupied indices. -/
theorem isZeckendorfRep_lex_iff_sum_fib_lt {l k : List ℕ}
    (hl : l.IsZeckendorfRep) (hk : k.IsZeckendorfRep) :
    List.Lex (· < ·) l k ↔
      (l.map Nat.fib).sum < (k.map Nat.fib).sum := by
  constructor
  · exact sum_fib_lt_of_lex hl hk
  · intro hsum
    have hne : l ≠ k := by
      intro h
      subst k
      exact Nat.lt_irrefl _ hsum
    rcases lt_or_gt_of_ne hne with hlk | hkl
    · exact (List.lt_iff_lex_lt l k).1 hlk
    · have hreverse := sum_fib_lt_of_lex hk hl
        ((List.lt_iff_lex_lt k l).1 hkl)
      omega

/-- Mathlib's greatest-index-first Zeckendorf representation is an order
embedding from naturals to lists with lexicographic order. -/
theorem zeckendorf_lex_iff_lt (m n : ℕ) :
    List.Lex (· < ·) (Nat.zeckendorf m) (Nat.zeckendorf n) ↔ m < n := by
  simpa using isZeckendorfRep_lex_iff_sum_fib_lt
    (Nat.isZeckendorfRep_zeckendorf m)
    (Nat.isZeckendorfRep_zeckendorf n)

end D5.S1.Words
