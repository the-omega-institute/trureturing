/- GID: D5/S3/Arith/SumInConcatenation/DecimalMultiples
   generality: G
   mirror-B: D5/B/S3/Arith/SumInConcatenation/DecimalMultiples
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.GCD.Basic]
   utility: none
   digest: The original A359482 sequence contains exactly 10 among 10,20,...,90. -/
import D5.S3.Arith.SumInConcatenation
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.IntervalCases

namespace D5.S3.Arith.SumInConcatenation.DecimalMultiples

open D5.S3.Arith.SumInConcatenation

/-- Hasler's three-position argument, with the middle case retaining x = m. -/
theorem legal_multiple_ten_iff (x m : ℕ) (hx : 0 < x)
    (hm : 0 < m ∧ m < 10) : Legal x (10 * m) ↔ x = m := by
  have hmlo := hm.1
  have hmhi := hm.2
  constructor
  · intro h
    have hy : 0 < 10 * m := by omega
    have hin : (Nat.digits 10 (x + 10 * m)).IsInfix
        (Nat.digits 10 (10 * m) ++ Nat.digits 10 x) := by
      simp only [Legal, D, Nat.ne_of_gt hx, Nat.ne_of_gt hy,
        show x + 10 * m ≠ 0 by omega, ↓reduceIte] at h
      rwa [← List.reverse_append, List.reverse_infix] at h
    have hd : Nat.digits 10 (10 * m) = [0, m] := by
      interval_cases m <;> norm_num at hm ⊢
    rw [hd] at hin
    simp only [List.cons_append, List.nil_append] at hin
    have hlen := Nat.le_length_digits_le 10 x (x + 10 * m) (by omega)
    let q := 10 ^ (Nat.digits 10 (x + 10 * m)).length
    have hsumlt : x + 10 * m < q :=
      Nat.lt_base_pow_length_digits (by decide)
    have hxlt : x < q := by omega
    rcases List.infix_cons_iff.mp hin with hp | hi
    · obtain ⟨r, hr⟩ := hp
      have hv := congrArg (Nat.ofDigits 10) hr
      simp only [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_cons,
        zero_add] at hv
      have heq : 99 * x = q * Nat.ofDigits 10 r := by dsimp [q]; omega
      have hcop : Nat.Coprime q 99 := (show Nat.Coprime 10 99 by decide).pow_left _
      have hdiv : q ∣ x := hcop.dvd_of_dvd_mul_left ⟨Nat.ofDigits 10 r, heq⟩
      have := Nat.le_of_dvd hx hdiv
      omega
    · rcases List.infix_cons_iff.mp hi with hp | hi
      · obtain ⟨r, hr⟩ := hp
        have hv := congrArg (Nat.ofDigits 10) hr
        simp only [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_cons] at hv
        have hmx : m ≤ x := by omega
        have heq : 9 * (x - m) = q * Nat.ofDigits 10 r := by dsimp [q]; omega
        have hcop : Nat.Coprime q 9 := (show Nat.Coprime 10 9 by decide).pow_left _
        have hdiv : q ∣ x - m := hcop.dvd_of_dvd_mul_left ⟨Nat.ofDigits 10 r, heq⟩
        by_cases he : x - m = 0
        · omega
        · have := Nat.le_of_dvd (by omega : 0 < x - m) hdiv
          omega
      · have he := hi.eq_of_length_le hlen
        have := Nat.digits.injective 10 he
        omega
  · intro he
    subst x
    interval_cases m <;> norm_num at hm ⊢ <;> decide

/-- None of 20,30,...,90 is a term of the original greedy sequence. -/
theorem sequence_ne_multiple_ten (n m : ℕ) (hm : 2 ≤ m ∧ m < 10) :
    seq n ≠ 10 * m := by
  intro he
  by_cases hn : n ≤ 1
  · have hs : seq n = 1 := by simp [seq, show n - 1 = 0 by omega, state]
    omega
  · have hn' : 1 ≤ n - 1 := by omega
    have hl := sequence_legal (n - 1) hn'
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), he] at hl
    have hx := (legal_multiple_ten_iff (seq (n - 1)) m
      (sequence_pos _) ⟨by omega, hm.2⟩).mp hl
    by_cases hfirst : n - 1 = 1
    · have hs : seq (n - 1) = 1 := by simp [hfirst, seq, state]
      omega
    · have := sequence_tail_ge_ten (n - 1) (by omega)
      omega

/-- The original least-unused rule chooses 10 immediately after the initial 1. -/
private theorem sequence_second : seq 2 = 10 := by
  apply Nat.le_antisymm
  · rw [show 2 = 0 + 2 by omega, sequence_greedy]
    apply Nat.sInf_le
    norm_num [seq, state]
    decide
  · exact sequence_tail_ge_ten 2 (by decide)

/-- The original sequence starts with 1,10 and contains exactly 10 among 10,20,...,90. -/
theorem sequence_multiple_ten_classification :
    seq 2 = 10 ∧ ∀ m : ℕ, 0 < m ∧ m < 10 →
      ((∃ n, 1 ≤ n ∧ seq n = 10 * m) ↔ m = 1) := by
  refine ⟨sequence_second, ?_⟩
  intro m hm
  constructor
  · rintro ⟨n, _, hn⟩
    by_contra h
    exact sequence_ne_multiple_ten n m ⟨by omega, hm.2⟩ hn
  · rintro rfl
    exact ⟨2, by decide, by simpa using sequence_second⟩

#print axioms legal_multiple_ten_iff
#print axioms sequence_ne_multiple_ten
#print axioms sequence_second
#print axioms sequence_multiple_ten_classification

end D5.S3.Arith.SumInConcatenation.DecimalMultiples
