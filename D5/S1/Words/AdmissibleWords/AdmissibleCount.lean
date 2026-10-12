/- GID: D5/S1/Words/AdmissibleWords/AdmissibleCount
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/AdmissibleCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeckendorf-admissible binary words of length m — those with no two consecutive true letters — are counted by the Fibonacci number F(m+2). The proof splits an admissible word of length m+2 on its first letter into a bijection with admissible words of length m+1 (first letter false) and length m (first letters true, false), giving the Fibonacci recurrence on the counts. -/

import Mathlib

open Nat

namespace D5.S1.Words.AdmissibleWords.AdmissibleCount

/-- A binary word `w : Fin m → Bool` is **admissible** (Zeckendorf) when it has no two consecutive
`true` letters. -/
def Adm : (m : ℕ) → (Fin m → Bool) → Prop
  | 0,     _ => True
  | 1,     _ => True
  | (m+2), w => (¬ (w 0 ∧ w 1)) ∧ Adm (m+1) (Fin.tail w)

instance decAdm : (m : ℕ) → (w : Fin m → Bool) → Decidable (Adm m w)
  | 0,     _ => .isTrue trivial
  | 1,     _ => .isTrue trivial
  | (m+2), w =>
      have : Decidable (Adm (m+1) (Fin.tail w)) := decAdm (m+1) (Fin.tail w)
      inferInstanceAs (Decidable ((¬ (w 0 ∧ w 1)) ∧ Adm (m+1) (Fin.tail w)))

theorem adm_two_iff (m : ℕ) (w : Fin (m+2) → Bool) :
    Adm (m+2) w ↔ (¬ (w 0 ∧ w 1)) ∧ Adm (m+1) (Fin.tail w) := Iff.rfl

theorem cons_one {m : ℕ} (a : Bool) (X : Fin (m+1) → Bool) :
    (Fin.cons a X : Fin (m+2) → Bool) (1 : Fin (m+2)) = X 0 := by
  rw [show (1 : Fin (m+2)) = Fin.succ 0 from (Fin.succ_zero_eq_one).symm, Fin.cons_succ]

theorem adm_cons_false (m : ℕ) (u : Fin m → Bool) :
    Adm (m+1) (Fin.cons false u) ↔ Adm m u := by
  cases m with
  | zero => simp [Adm]
  | succ k => rw [adm_two_iff]; simp [Fin.tail_cons, Fin.cons_zero]

theorem adm_tail_of_head_false (m : ℕ) (v : Fin (m+1) → Bool)
    (hv : Adm (m+1) v) (h0 : v 0 = false) : Adm m (Fin.tail v) := by
  have hcons : Fin.cons false (Fin.tail v) = v := by
    rw [← h0]; exact Fin.cons_self_tail v
  rw [← adm_cons_false, hcons]; exact hv

/-- Splitting an admissible word of length `m+2` on its first letter is a bijection with the
admissible words of length `m+1` (when the first letter is `false`) and length `m` (when the first
two letters are `true, false`). -/
def admEquiv (m : ℕ) :
    {w : Fin (m+2) → Bool // Adm (m+2) w} ≃
      ({v : Fin (m+1) → Bool // Adm (m+1) v} ⊕ {u : Fin m → Bool // Adm m u}) where
  toFun := fun ⟨w, hw⟩ =>
    if h0 : w 0 = true then
      Sum.inr ⟨Fin.tail (Fin.tail w), by
        have hw1 : w 1 = false := by
          cases hb : w 1 with
          | false => rfl
          | true => exact absurd ⟨h0, hb⟩ ((adm_two_iff m w).1 hw).1
        have h1 : (Fin.tail w) 0 = false := by
          simpa [Fin.tail, Fin.succ_zero_eq_one] using hw1
        exact adm_tail_of_head_false m (Fin.tail w) ((adm_two_iff m w).1 hw).2 h1⟩
    else
      Sum.inl ⟨Fin.tail w, ((adm_two_iff m w).1 hw).2⟩
  invFun := fun s => match s with
    | Sum.inl ⟨v, hv⟩ => ⟨Fin.cons false v, by
        rw [adm_two_iff]
        exact ⟨by simp [Fin.cons_zero], by simpa [Fin.tail_cons] using hv⟩⟩
    | Sum.inr ⟨u, hu⟩ => ⟨Fin.cons true (Fin.cons false u), by
        rw [adm_two_iff]
        refine ⟨?_, ?_⟩
        · rw [cons_one]; simp [Fin.cons_zero]
        · simpa [Fin.tail_cons] using (adm_cons_false m u).2 hu⟩
  left_inv := by
    rintro ⟨w, hw⟩
    by_cases h0 : w 0 = true
    · simp only [h0, dif_pos]
      apply Subtype.ext
      have hw1 : w 1 = false := by
        cases hb : w 1 with
        | false => rfl
        | true => exact absurd ⟨h0, hb⟩ ((adm_two_iff m w).1 hw).1
      have e1 : Fin.cons false (Fin.tail (Fin.tail w)) = Fin.tail w := by
        have h1 : (Fin.tail w) 0 = false := by
          simpa [Fin.tail, Fin.succ_zero_eq_one] using hw1
        rw [← h1]; exact Fin.cons_self_tail (Fin.tail w)
      have e0 : Fin.cons true (Fin.tail w) = w := by
        rw [← h0]; exact Fin.cons_self_tail w
      show Fin.cons true (Fin.cons false (Fin.tail (Fin.tail w))) = w
      rw [e1, e0]
    · simp only [h0]
      apply Subtype.ext
      have h0' : w 0 = false := by simpa using h0
      show Fin.cons false (Fin.tail w) = w
      rw [← h0']; exact Fin.cons_self_tail w
  right_inv := by
    rintro (⟨v, hv⟩ | ⟨u, hu⟩)
    · simp [Fin.cons_zero, Fin.tail_cons]
    · simp [Fin.cons_zero, Fin.tail_cons]

/-- The count of admissible words of length `m+2` is the sum of the counts at lengths `m+1` and `m`
— the Fibonacci recurrence, read off the splitting bijection. -/
theorem wcount_succ_succ (m : ℕ) :
    Fintype.card {w : Fin (m+2) → Bool // Adm (m+2) w}
      = Fintype.card {v : Fin (m+1) → Bool // Adm (m+1) v}
        + Fintype.card {u : Fin m → Bool // Adm m u} := by
  rw [Fintype.card_congr (admEquiv m), Fintype.card_sum]

/-- **Zeckendorf-admissible word count.** The number of binary words of length `m` with no two
consecutive `true` letters is the Fibonacci number `F(m+2)` (with `F 0 = 0`, `F 1 = 1`). -/
theorem admissibleWord_card_eq_fib (m : ℕ) :
    Fintype.card {w : Fin m → Bool // Adm m w} = Nat.fib (m + 2) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => decide
    | 1 => decide
    | (k + 2) =>
        rw [wcount_succ_succ k, ih (k + 1) (by omega), ih k (by omega)]
        show Nat.fib (k + 3) + Nat.fib (k + 2) = Nat.fib (k + 4)
        have h : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) :=
          Nat.fib_add_two (n := k + 2)
        omega

end D5.S1.Words.AdmissibleWords.AdmissibleCount
