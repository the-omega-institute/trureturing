/- GID: D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas, mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Tactic.Positivity]
   utility: none
   digest: Wu and Lou's permutation-invariant decimal Niven digit-sum bound. -/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Positivity

namespace D5.S1.Digit.Admissibility.WuLouPermutationInvariantNivenDigitSum

structure DecimalPINN where
  digits : List Nat
  nonempty : digits ≠ []
  leading_ne_zero : digits.getLast nonempty ≠ 0
  digit_lt_ten : ∀ x ∈ digits, x < 10
  permutation_divisibility :
    ∀ e : List Nat, e.Perm digits → digits.sum ∣ Nat.ofDigits 10 e

theorem result
    (d : DecimalPINN)
    (htwo : 2 ≤ d.digits.countP (· != 0))
    (hdistinct : ∃ a ∈ d.digits, ∃ b ∈ d.digits, a ≠ b) :
    3 ∣ d.digits.sum ∧ 3 ≤ d.digits.sum ∧ d.digits.sum ≤ 81 := by
  have ordered_digit_sum_bound : ∀ {a b : Nat} {rest : List Nat},
      d.digits.Perm (a :: b :: rest) → a < b →
        3 ∣ d.digits.sum ∧ 3 ≤ d.digits.sum ∧ d.digits.sum ≤ 81 := by
    intro a b rest hperm hab
    have swapped_digits_dvd : d.digits.sum ∣ 9 * (b - a) := by
      have hfirst : d.digits.sum ∣ Nat.ofDigits 10 (a :: b :: rest) :=
        d.permutation_divisibility _ hperm.symm
      have hsecond : d.digits.sum ∣ Nat.ofDigits 10 (b :: a :: rest) :=
        d.permutation_divisibility _ ((List.Perm.swap a b rest).trans hperm.symm)
      have hdifference := Nat.dvd_sub hfirst hsecond
      have hvalue :
          Nat.ofDigits 10 (a :: b :: rest) - Nat.ofDigits 10 (b :: a :: rest) =
            9 * (b - a) := by
        simp only [Nat.ofDigits_cons]
        omega
      rwa [hvalue] at hdifference
    have ha_mem : a ∈ d.digits := hperm.mem_iff.mpr (by simp)
    have hb_mem : b ∈ d.digits := hperm.mem_iff.mpr (by simp)
    have ha_lt : a < 10 := d.digit_lt_ten a ha_mem
    have hb_lt : b < 10 := d.digit_lt_ten b hb_mem
    have hsum : d.digits.sum = a + (b + rest.sum) := by
      simpa using hperm.sum_eq
    have hdelta_pos : 0 < b - a := Nat.sub_pos_of_lt hab
    have hdelta_lt_sum : b - a < d.digits.sum := by
      by_cases ha : a = 0
      · have hb : b ≠ 0 := by omega
        have hcount := hperm.countP_eq (· != 0)
        have hrest_count : 0 < rest.countP (· != 0) := by
          simp [ha, hb] at hcount
          omega
        rcases List.countP_pos_iff.mp hrest_count with ⟨c, hc, hc_ne⟩
        have hc_ne_zero : c ≠ 0 := by simpa using hc_ne
        have hc_pos : 0 < c := Nat.pos_of_ne_zero hc_ne_zero
        have hc_le : c ≤ rest.sum := List.le_sum_of_mem hc
        omega
      · omega
    have hupper : d.digits.sum ≤ 81 := by
      have hle : d.digits.sum ≤ 9 * (b - a) :=
        Nat.le_of_dvd (by positivity) swapped_digits_dvd
      omega
    have hthree : 3 ∣ d.digits.sum := by
      by_contra hnot
      have hcop_three : Nat.Coprime d.digits.sum 3 :=
        ((Nat.prime_three.coprime_iff_not_dvd).mpr hnot).symm
      have hcop_nine : Nat.Coprime d.digits.sum 9 := by
        simpa using hcop_three.pow_right 2
      have hdelta_dvd : d.digits.sum ∣ b - a :=
        hcop_nine.dvd_of_dvd_mul_left swapped_digits_dvd
      have := Nat.le_of_dvd hdelta_pos hdelta_dvd
      omega
    have hlower : 3 ≤ d.digits.sum := by
      exact Nat.le_of_dvd (by omega) hthree
    exact ⟨hthree, hlower, hupper⟩
  rcases hdistinct with ⟨a, ha, b, hb, hab⟩
  have hb_erase : b ∈ d.digits.erase a :=
    (List.mem_erase_of_ne hab.symm).mpr hb
  let rest := (d.digits.erase a).erase b
  have hperm_a : d.digits.Perm (a :: d.digits.erase a) :=
    List.perm_cons_erase ha
  have hperm_b : (d.digits.erase a).Perm (b :: rest) := by
    exact List.perm_cons_erase hb_erase
  have hperm : d.digits.Perm (a :: b :: rest) :=
    hperm_a.trans (hperm_b.cons a)
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · exact ordered_digit_sum_bound hperm hab_lt
  · exact ordered_digit_sum_bound
      (hperm.trans (List.Perm.swap a b rest).symm) hba_lt

example :
    ∃ d : DecimalPINN,
      2 ≤ d.digits.countP (· != 0) ∧
        (∃ a ∈ d.digits, ∃ b ∈ d.digits, a ≠ b) := by
  let positiveControl : DecimalPINN := {
    digits := [6, 2, 1]
    nonempty := by simp
    leading_ne_zero := by simp
    digit_lt_ten := by simp
    permutation_divisibility := by
      intro e he
      have hsum : e.sum = 9 := by simpa using he.sum_eq
      rw [Nat.dvd_iff_mod_eq_zero]
      rw [Nat.ofDigits_mod]
      norm_num [Nat.ofDigits_one, hsum]
  }
  refine ⟨positiveControl, ?_, ?_⟩
  · norm_num [positiveControl]
  · exact ⟨6, by simp [positiveControl], 2, by simp [positiveControl], by norm_num⟩

end D5.S1.Digit.Admissibility.WuLouPermutationInvariantNivenDigitSum
