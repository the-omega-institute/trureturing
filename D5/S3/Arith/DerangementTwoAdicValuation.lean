/- GID: D5/S3/Arith/DerangementTwoAdicValuation
   generality: G
   mirror-B: D5/B/S3/Arith/DerangementTwoAdicValuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derangement parity and valuation exclude nontrivial powers at indices 3 mod 4. -/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace D5.S3.Arith.DerangementTwoAdicValuation

private theorem numDerangements_odd_iff_even :
    ∀ n : ℕ, Odd (numDerangements n) ↔ Even n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n hn hn1 =>
      rw [numDerangements_add_two]
      grind [Nat.odd_mul, Nat.odd_add]

private theorem numDerangements_add_succ_odd (n : ℕ) :
    Odd (numDerangements n + numDerangements (n + 1)) := by
  rw [Nat.odd_add]
  grind [numDerangements_odd_iff_even]

private theorem padicValNat_two_numDerangements_eq {n : ℕ} (hn : 2 ≤ n) :
    padicValNat 2 (numDerangements n) = padicValNat 2 (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 m] at ⊢
  rw [numDerangements_add_two]
  have hsum : Odd (numDerangements m + numDerangements (m + 1)) :=
    numDerangements_add_succ_odd m
  have hsum_ne : numDerangements m + numDerangements (m + 1) ≠ 0 := by
    intro hzero
    apply hsum.not_two_dvd_nat
    simp [hzero]
  rw [padicValNat.mul (by omega) hsum_ne,
    padicValNat.eq_zero_of_not_dvd hsum.not_two_dvd_nat]
  simp

/-- Miska's parity law and exact two-adic valuation identity for derangement numbers. -/
theorem numDerangements_two_adic_valuation :
    (∀ n : ℕ, Odd (numDerangements n) ↔ Even n) ∧
      (∀ n : ℕ, 2 ≤ n →
        padicValNat 2 (numDerangements n) = padicValNat 2 (n - 1)) := by
  exact ⟨numDerangements_odd_iff_even, fun _ hn => padicValNat_two_numDerangements_eq hn⟩

private theorem numDerangements_power_exponent_dvd {n b k : ℕ} (hn : 2 ≤ n)
    (hpower : numDerangements n = b ^ k) :
    k ∣ padicValNat 2 (n - 1) := by
  rw [← numDerangements_two_adic_valuation.2 n hn, hpower, padicValNat.pow]
  exact dvd_mul_right k (padicValNat 2 b)

/-- Derangement numbers are odd exactly at even indices; from index two onward
their exact two-adic valuation is that of the preceding index; consequently,
whenever a derangement number is a natural-number power, its exponent divides
that valuation. -/
theorem numDerangements_parity_valuation_and_power_exponent :
    (∀ n : ℕ, Odd (numDerangements n) ↔ Even n) ∧
      (∀ n : ℕ, 2 ≤ n →
        padicValNat 2 (numDerangements n) = padicValNat 2 (n - 1)) ∧
      ∀ n b k : ℕ, 2 ≤ n →
        numDerangements n = b ^ k →
        k ∣ padicValNat 2 (n - 1) := by
  refine ⟨numDerangements_two_adic_valuation.1, numDerangements_two_adic_valuation.2, ?_⟩
  intro n b k hn hpower
  exact numDerangements_power_exponent_dvd hn hpower

/-- Four times a natural index plus two has two-adic valuation one. -/
theorem padicValNat_two_four_mul_add_two (t : Nat) :
    padicValNat 2 (4 * t + 2) = 1 := by
  have hodd : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hnotdvd : ¬2 ∣ 2 * t + 1 := hodd.not_two_dvd_nat
  rw [show 4 * t + 2 = 2 * (2 * t + 1) by omega,
    padicValNat.mul (by norm_num) (by omega),
    padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd hnotdvd]

/-- A derangement number at an index congruent to three modulo four is not a
nontrivial natural-number power. -/
theorem numDerangements_four_mul_add_three_ne_pow (t b k : ℕ) (hk : 2 ≤ k) :
    numDerangements (4 * t + 3) ≠ b ^ k := by
  intro hpower
  have hdiv : k ∣ padicValNat 2 ((4 * t + 3) - 1) :=
    numDerangements_parity_valuation_and_power_exponent.2.2
      (4 * t + 3) b k (by omega) hpower
  have hval : padicValNat 2 ((4 * t + 3) - 1) = 1 := by
    simpa using padicValNat_two_four_mul_add_two t
  rw [hval] at hdiv
  have hk1 : k ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
  omega

end D5.S3.Arith.DerangementTwoAdicValuation
