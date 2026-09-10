/- GID: D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/TruncatedExponentialTwoAdic
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Six-step truncation and odd-power periodicity prove the positive-k valuation branches. -/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace D5.S3.Arith.Congruence.TruncatedExponentialTwoAdic

private def H (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => n ^ (m + 1) + (m + 1) * H n m

/-- The natural-number factorial quotient sum of OEIS A398187; k indexes the truncation. -/
def S (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n - k + 1), (n - k).factorial / j.factorial * n ^ j

private lemma h_sum (n m : ℕ) :
    H n m = ∑ j ∈ Finset.range (m + 1), m.factorial / j.factorial * n ^ j := by
  induction m with
  | zero => simp [H]
  | succ m ih =>
    rw [H, Finset.sum_range_succ, ih, Finset.mul_sum]
    simp only [Nat.div_self (Nat.factorial_pos _), one_mul]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hd := Nat.factorial_dvd_factorial (show j ≤ m by simpa using hj)
    rw [Nat.factorial_succ, Nat.mul_div_assoc _ hd, mul_assoc]

private lemma six_zero (x : ZMod 16) :
    (x+1)*(x+2)*(x+3)*(x+4)*(x+5)*(x+6) = 0 := by
  fin_cases x <;> decide

-- Six recursive steps leave a history coefficient divisible by 16.
private lemma six (n m : ℕ) : (H n (m+6) : ZMod 16) =
    (n : ZMod 16)^m * ((n : ZMod 16)^6 + (m+6) *
      ((n : ZMod 16)^5 + (m+5) * ((n : ZMod 16)^4 + (m+4) *
      ((n : ZMod 16)^3 + (m+3) * ((n : ZMod 16)^2 + (m+2) * (n : ZMod 16)))))) := by
  simp only [H, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp only [pow_add]
  have hz := six_zero (m : ZMod 16)
  linear_combination (H n m : ZMod 16) * hz

private lemma val_mod {a : ℕ} (ha : a % 16 ≠ 0) :
    padicValNat 2 a = padicValNat 2 (a % 16) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hv (b : ℕ) (hb : b ≠ 0) (h16 : ¬16 ∣ b) : padicValNat 2 b < 4 := by
    have := (padicValNat_dvd_iff_le (p := 2) (n := 4) hb).not.mp h16
    omega
  have hva := hv a ha0 (by simpa [Nat.dvd_iff_mod_eq_zero] using ha)
  have hvr := hv (a % 16) ha (by simpa [Nat.dvd_iff_mod_eq_zero] using ha)
  have he (t : ℕ) (ht : t ≤ 4) : 2 ^ t ∣ a % 16 ↔ 2 ^ t ∣ a :=
    Nat.dvd_mod_iff (show 2 ^ t ∣ 16 from pow_dvd_pow 2 ht)
  apply Nat.le_antisymm
  · exact (padicValNat_dvd_iff_le ha).mp ((he _ hva.le).mpr pow_padicValNat_dvd)
  · exact (padicValNat_dvd_iff_le ha0).mp ((he _ hvr.le).mp pow_padicValNat_dvd)

private lemma odd_four (x : ZMod 16) (hx : x.val % 2 = 1) : x ^ 4 = 1 := by
  fin_cases x <;> revert hx <;> decide

private lemma odd_pow (n m : ℕ) (hn : n % 2 = 1) :
    (n : ZMod 16)^m = (n : ZMod 16)^(m % 4) := by
  have hf : (n : ZMod 16)^4 = 1 := odd_four _ (by simpa [ZMod.val_natCast] using hn)
  exact pow_eq_pow_mod m hf

private def P (x y : ZMod 16) : ZMod 16 :=
  x^6 + (y+6)*(x^5+(y+5)*(x^4+(y+4)*(x^3+(y+3)*(x^2+(y+2)*x))))

private lemma large_table (x y : ZMod 16) (hx : x.val % 2 = 1)
    (hk : (x - y - 4).val ≠ 0) :
    (x^(y.val % 4) * P x y).val ≠ 0 ∧
    padicValNat 2 (x^(y.val % 4) * P x y).val = padicValNat 2 (x - y - 4).val := by
  revert hx hk
  fin_cases x <;> fin_cases y <;> decide +kernel

private def R (x : ZMod 16) : ℕ → ZMod 16
  | 0 => 1
  | m+1 => x^(m+1) + (m+1)*R x m

private lemma cast_h (n m : ℕ) : (H n m : ZMod 16) = R (n : ZMod 16) m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [H, R, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_one, ih]

private lemma small_table (x : ZMod 16) (m : Fin 6) (hx : x.val % 2 = 1)
    (hk : (x - m.val + 2).val ≠ 0) :
    (R x m).val ≠ 0 ∧
    padicValNat 2 (R x m).val = padicValNat 2 (x - m.val + 2).val := by
  revert hx hk
  fin_cases x <;> fin_cases m <;> decide +kernel

-- The two branches cover every truncation length; the table never bounds n or k.
private lemma all_residues (n k : ℕ) (hn : n % 2 = 1) (hkn : k ≤ n)
    (hk : k % 16 ≠ 14) :
    (H n (n-k)) % 16 ≠ 0 ∧
    padicValNat 2 ((H n (n-k)) % 16) = padicValNat 2 ((k+2) % 16) := by
  have hx : (n : ZMod 16).val % 2 = 1 := by simpa [ZMod.val_natCast] using hn
  have hk0 : (k+2) % 16 ≠ 0 := by omega
  by_cases hm : 6 ≤ n-k
  · obtain ⟨m, he⟩ := Nat.exists_eq_add_of_le hm
    have he' : n-k = m+6 := by omega
    have hcast : (n : ZMod 16) - (m : ZMod 16) - 4 = ((k+2 : ℕ) : ZMod 16) := by
      have hnmk : n = m+6+k := by omega
      rw [hnmk]
      push_cast
      ring
    have ht := large_table (n : ZMod 16) (m : ZMod 16) hx
      (by simpa only [hcast, ZMod.val_natCast] using hk0)
    have hh : (H n (n-k) : ZMod 16) =
        (n : ZMod 16)^((m : ZMod 16).val % 4) * P (n : ZMod 16) (m : ZMod 16) := by
      rw [he', six, odd_pow n m hn]
      simp [P, ZMod.val_natCast]
    rw [← hh] at ht
    simpa only [hcast, ZMod.val_natCast] using ht
  · have hcast : (n : ZMod 16) - ((n-k : ℕ) : ZMod 16) + 2 =
        ((k+2 : ℕ) : ZMod 16) := by
      rw [Nat.cast_sub hkn]
      push_cast
      ring
    have ht := small_table (n : ZMod 16) ⟨n-k, by omega⟩ hx
      (by simpa only [hcast, ZMod.val_natCast] using hk0)
    simpa only [← cast_h, hcast, ZMod.val_natCast] using ht

-- Nonzero residues determine the exact valuation, since it is strictly below four.
private lemma full_val (n k : ℕ) (hn : n % 2 = 1) (hkn : k ≤ n) (hk : k % 16 ≠ 14) :
    padicValNat 2 (S n k) = padicValNat 2 (k+2) := by
  have hh := all_residues n k hn hkn hk
  rw [S, ← h_sum, val_mod hh.1, hh.2, ← val_mod (show (k+2) % 16 ≠ 0 by omega)]

/-- Both positive-k branches conjectured in OEIS A398189, for every odd n. -/
theorem odd_positive_branches (n k : ℕ) (hn : Odd n) (_hkpos : 1 ≤ k) (hkn : k ≤ n) :
    (Odd k → padicValNat 2 (S n k) = 0) ∧
    (Even k → k % 16 ≠ 14 → padicValNat 2 (S n k) = padicValNat 2 (k+2)) := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  constructor
  · intro hk
    have hk2 : k % 2 = 1 := Nat.odd_iff.mp hk
    rw [full_val n k hn2 hkn (by omega)]
    apply padicValNat.eq_zero_of_not_dvd
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  · intro _ hk
    exact full_val n k hn2 hkn hk

#print axioms odd_positive_branches
end D5.S3.Arith.Congruence.TruncatedExponentialTwoAdic
