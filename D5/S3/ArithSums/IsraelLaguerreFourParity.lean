/- GID: D5/S3/ArithSums/IsraelLaguerreFourParity
   generality: I
   mirror-B: D5/B/S3/ArithSums/IsraelLaguerreFourParity
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Padics.PadicVal.Basic]
   utility: none
   digest: Laguerre(n,4) has odd reduced numerator and denominator for every natural n. -/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.IsraelLaguerreFourParity

/-!
OEIS A160627: "Conjecture: all terms are odd. - _Robert Israel_, Mar 29 2018"
OEIS A160628: "Conjecture: all terms are odd. - _Robert Israel_, Mar 29 2018"
-/

open scoped BigOperators

def L (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℚ) * (-4 : ℚ) ^ k / (Nat.factorial k : ℚ)

theorem result : ∀ n : ℕ, Odd (L n).num ∧ Odd (L n).den := by
  intro n
  let F : ℕ → ℚ := fun k ↦
    (Nat.choose n k : ℚ) * (-4 : ℚ) ^ k / (Nat.factorial k : ℚ)
  let tail : ℚ := ∑ i ∈ Finset.range n, F (i + 1)
  have hsplit : L n = 1 + tail := by
    simp [L, tail, F, Finset.sum_range_succ', add_comm]
  have hterm (i : ℕ) (hi : i < n) : 0 < padicValRat 2 (F (i + 1)) := by
    have hkn : i + 1 ≤ n := by omega
    have hchoose : Nat.choose n (i + 1) ≠ 0 := Nat.choose_ne_zero hkn
    have hchooseQ : (Nat.choose n (i + 1) : ℚ) ≠ 0 := by exact_mod_cast hchoose
    have hpowQ : (-4 : ℚ) ^ (i + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hfactorialQ : (Nat.factorial (i + 1) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (i + 1)
    have hfactorial :=
      padicValNat_factorial_lt_of_ne_zero 2 (show i + 1 ≠ 0 by omega)
    have hfour : padicValRat 2 (-4 : ℚ) = 2 := by
      rw [padicValRat.neg]
      rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
      rw [show 4 = 2 ^ 2 by norm_num, padicValNat.pow, padicValNat_self]
      norm_num
    dsimp only [F]
    rw [padicValRat.div (mul_ne_zero hchooseQ hpowQ) hfactorialQ,
      padicValRat.mul hchooseQ hpowQ, padicValRat.pow, hfour,
      padicValRat.of_nat, padicValRat.of_nat]
    omega
  have hval_and_ne : padicValRat 2 (L n) = 0 ∧ L n ≠ 0 := by
    by_cases htail : tail = 0
    · simp [hsplit, htail]
    · have htailVal : 0 < padicValRat 2 tail := by
        apply padicValRat.sum_pos_of_pos (p := 2) (n := n)
        · intro i hi
          exact hterm i hi
        · exact htail
      have hsum_ne : (1 : ℚ) + tail ≠ 0 := by
        intro hzero
        have htail_eq : tail = -1 := by linarith
        rw [htail_eq, padicValRat.neg, padicValRat.one] at htailVal
        omega
      have hval_lt : padicValRat 2 (1 : ℚ) < padicValRat 2 tail := by
        simpa using htailVal
      constructor
      · rw [hsplit]
        simpa using
          padicValRat.add_eq_of_lt (p := 2) hsum_ne (by norm_num) htail hval_lt
      · rw [hsplit]
        exact hsum_ne
  rw [padicValRat_def] at hval_and_ne
  have heqInt : (padicValInt 2 (L n).num : ℤ) = padicValNat 2 (L n).den :=
    sub_eq_zero.mp hval_and_ne.1
  have heq : padicValInt 2 (L n).num = padicValNat 2 (L n).den := by
    exact_mod_cast heqInt
  have hnum_ne : (L n).num ≠ 0 := Rat.num_ne_zero.mpr hval_and_ne.2
  have hnum_abs_ne : (L n).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum_ne
  have hdenval : padicValNat 2 (L n).den = 0 := by
    by_contra hdenval
    have hdendvd : 2 ∣ (L n).den :=
      (dvd_iff_padicValNat_ne_zero (L n).den_nz).mpr hdenval
    have hnumval : padicValNat 2 (L n).num.natAbs ≠ 0 := by
      simpa only [padicValInt] using heq.trans_ne hdenval
    have hnumdvd : 2 ∣ (L n).num.natAbs :=
      (dvd_iff_padicValNat_ne_zero hnum_abs_ne).mpr hnumval
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hnumdvd hdendvd) (L n).reduced
  have hnumval : padicValInt 2 (L n).num = 0 := heq.trans hdenval
  have hnum_not_dvd : ¬(2 : ℤ) ∣ (L n).num := by
    rcases padicValInt.eq_zero_iff.mp hnumval with h | h | h
    · norm_num at h
    · exact (hnum_ne h).elim
    · exact h
  have hden_not_dvd : ¬2 ∣ (L n).den := by
    intro hdendvd
    exact ((dvd_iff_padicValNat_ne_zero (L n).den_nz).mp hdendvd) hdenval
  constructor
  · rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    exact hnum_not_dvd
  · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hden_not_dvd

#print axioms L
#print axioms result

end D5.S3.ArithSums.IsraelLaguerreFourParity
