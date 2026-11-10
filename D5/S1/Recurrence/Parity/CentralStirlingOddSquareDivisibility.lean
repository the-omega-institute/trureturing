/- GID: D5/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Odd central Stirling numbers are divisible by the square of their column. -/

/-
admission_basis: open-problem-resolution (#22943; Proved)
escape_witness: none
claim: definition; the literal natural-index assertion in OEIS A007820.
stirling_reflection: proof_shape: bind-only; consumer: odd_square_dvd;
  escape_witness: none. Inclusion-exclusion, binomial reflection and normalization.
odd_square_dvd: proof_shape: bind-only; consumer: result; escape_witness: none.
  Reflection, finite-sum divisibility and cancellation of the coprime factor 2.
result: proof_shape: bind-only; consumer: settling result; escape_witness: none.
  Instantiates odd_square_dvd at 2*n+1.
Direct frozen dependencies: stirling_reflection, odd_square_dvd and result use
  D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion
  declaration statement_id: sha256:2508e114d7ae0d003f3f1c2ca5079a26811c8ed501add6239b68109ce2a28efb
  after the same-module helpers are expanded; claim has none.
The claim uses Nat.stirlingSecond directly and introduces no sequence alias.
Source: https://oeis.org/A007820, COMMENTS, Peter Bala.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25728
-/

import D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod

namespace D5.S1.Recurrence.Parity.CentralStirlingOddSquareDivisibility

/- OEIS A007820 defines a(n) = S(2n,n). Mathlib's Nat.stirlingSecond r k
counts partitions of an r-element set into exactly k nonempty subsets.
The source sequence is explicit, so no existence premise or new sequence
definition is needed. The conjecture includes n = 0. -/
def claim : Prop :=
  ∀ (n : ℕ), (2 * n + 1) ^ 2 ∣
    Nat.stirlingSecond (2 * (2 * n + 1)) (2 * n + 1)

end D5.S1.Recurrence.Parity.CentralStirlingOddSquareDivisibility

open Finset
open D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod

namespace D5.S1.Recurrence.Parity.CentralStirlingOddSquareDivisibility

private theorem stirling_reflection (m : ℕ) :
    (Nat.stirlingSecond (2 * m) m : ℤ) =
      ∑ j ∈ range (2 * m + 1), (-1 : ℤ) ^ (m + j) *
        (Nat.choose (2 * m) j : ℤ) * (m : ℤ) ^ j *
        (Nat.stirlingSecond (2 * m - j) m : ℤ) := by
  apply mul_left_cancel₀ (a := (m.factorial : ℤ))
    (by exact_mod_cast Nat.factorial_ne_zero m)
  rw [stirling2_inclusion_exclusion]
  calc
    ∑ i ∈ range (m + 1), (-1 : ℤ) ^ (m - i) * (Nat.choose m i : ℤ) * (i : ℤ) ^ (2 * m) =
        ∑ i ∈ range (m + 1), (-1 : ℤ) ^ i * (Nat.choose m i : ℤ) *
          ((m : ℤ) - (i : ℤ)) ^ (2 * m) := by
      conv_lhs => rw [← sum_range_reflect]
      apply sum_congr rfl
      intro i hi
      have hi : i ≤ m := by exact mem_range_succ_iff.mp hi
      simp only [Nat.add_sub_cancel, Nat.sub_sub_self hi, Nat.choose_symm hi,
        Nat.cast_sub hi]
    _ = ∑ j ∈ range (2 * m + 1),
        ((-1 : ℤ) ^ (m + j) * (Nat.choose (2 * m) j : ℤ) * (m : ℤ) ^ j) *
          (∑ i ∈ range (m + 1), (-1 : ℤ) ^ (m - i) *
            (Nat.choose m i : ℤ) * (i : ℤ) ^ (2 * m - j)) := by
      simp_rw [sub_pow, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro i hi
      have hi : i ≤ m := by exact mem_range_succ_iff.mp hi
      have hs : (-1 : ℤ) ^ i * (-1 : ℤ) ^ (j + 2 * m) =
          (-1 : ℤ) ^ (m + j) * (-1 : ℤ) ^ (m - i) := by
        simp only [← pow_add]
        apply neg_one_pow_congr
        simp only [Nat.even_iff]
        omega
      calc
        _ = ((-1 : ℤ) ^ i * (-1 : ℤ) ^ (j + 2 * m)) *
            ((Nat.choose m i : ℤ) * (m : ℤ) ^ j *
              (i : ℤ) ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ)) := by ring
        _ = _ := by rw [hs]; ring
    _ = (m.factorial : ℤ) *
        ∑ j ∈ range (2 * m + 1), (-1 : ℤ) ^ (m + j) *
          (Nat.choose (2 * m) j : ℤ) * (m : ℤ) ^ j *
          (Nat.stirlingSecond (2 * m - j) m : ℤ) := by
      simp_rw [← stirling2_inclusion_exclusion, mul_sum]
      apply sum_congr rfl
      intro j hj
      ring

private theorem odd_square_dvd (m : ℕ) (hm : Odd m) :
    m ^ 2 ∣ Nat.stirlingSecond (2 * m) m := by
  have he := stirling_reflection m
  rw [sum_range_succ'] at he
  simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_zero,
    Nat.sub_zero, hm.neg_one_pow, neg_mul, one_mul] at he
  have hsum : (m : ℤ) ^ 2 ∣
      ∑ j ∈ range (2 * m), (-1 : ℤ) ^ (m + (j + 1)) *
        (Nat.choose (2 * m) (j + 1) : ℤ) * (m : ℤ) ^ (j + 1) *
        (Nat.stirlingSecond (2 * m - (j + 1)) m : ℤ) := by
    apply dvd_sum
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [zero_add, Nat.choose_one_right, Nat.cast_mul, Nat.cast_ofNat, pow_one]
      refine ⟨(-1 : ℤ) ^ (m + 1) * 2 *
        (Nat.stirlingSecond (2 * m - 1) m : ℤ), ?_⟩
      ring
    · exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (pow_dvd_pow (m : ℤ) (by omega : 2 ≤ j + 1)) _) _
  have hd : (m : ℤ) ^ 2 ∣ (2 : ℤ) * (Nat.stirlingSecond (2 * m) m : ℤ) := by
    convert hsum using 1
    linarith [he]
  have hdNat : m ^ 2 ∣ 2 * Nat.stirlingSecond (2 * m) m := by
    exact Int.ofNat_dvd.mp hd
  exact (hm.coprime_two_right.pow_left 2).dvd_of_dvd_mul_left hdNat

theorem result : D5.S1.Recurrence.Parity.CentralStirlingOddSquareDivisibility.claim := by
  intro n
  exact odd_square_dvd (2 * n + 1) ⟨n, by omega⟩

end D5.S1.Recurrence.Parity.CentralStirlingOddSquareDivisibility
