/- GID: D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Affine vanishing-diagonal exponents divide their own integer coefficients. -/

import D5.S1.Recurrence.Residue.DiagonalVanishingIndexDivisibility

/-!
For slope d, use the already constructed series
`A = NegativePowerDiagonalModPrime.generatingSeries (d + 1)`.
Its generating_equation proves A(0) = A'(0) = 1 and, for n > 1,
`[x^n] A(x / A(x)^(d*(n-1)+1)) = 0`; generating_unique characterizes it.
The coefficient is NegativePowerDiagonalModPrime.a (d + 1) n, since that
construction uses parameter p and exponent (p-1)*(n-1)+1.

The affine difference e(n)-e(m)=d*(n-m) transfers the derivative coefficient
identity to divisibility of each summand in the triangular equation.
Strong induction then proves that e(n) divides the nth coefficient.
The slope-two instance proves only the divisibility conjecture of A395833;
the distinct mod-three clause is not asserted here.
Source: `Library/ArithSums/hanna2026a395833div.md`.
-/

open PowerSeries
namespace D5.S1.Recurrence.Residue.DiagonalExponentSelfDivisibility

private theorem coeff_diagonal (A : PowerSeries ℤ) (e n : ℕ) :
    coeff n (A.subst (X * invOfUnit A 1 ^ e)) =
      coeff n A + ∑ j ∈ Finset.range n,
        coeff j A * coeff (n - j) (invOfUnit A 1 ^ (e * j)) := by
  have hz : constantCoeff (X * invOfUnit A 1 ^ e) = 0 := by simp
  rw [coeff_subst' (.of_constantCoeff_zero hz)]
  have ht (j : ℕ) :
      coeff j A • coeff n ((X * invOfUnit A 1 ^ e) ^ j) =
        if j ≤ n then coeff j A * coeff (n - j) (invOfUnit A 1 ^ (e * j)) else 0 := by
    rw [mul_pow, ← pow_mul, coeff_X_pow_mul']
    split_ifs <;> simp
  simp_rw [ht]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · rw [Finset.sum_range_succ]
    have he : coeff n A * coeff (n - n) (invOfUnit A 1 ^ (e * n)) = coeff n A := by
      simp
    simp only [le_refl, if_true, he]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    have hjn : j ≤ n := by
      by_contra h
      simp [h] at hj
    exact Finset.mem_range.mpr (by omega)


private theorem inverse_power_dvd (A : PowerSeries ℤ) (hA : constantCoeff A = 1)
    (N j : ℕ) (hj : 0 < j) :
    (N : ℤ) ∣ (j : ℤ) * coeff j (invOfUnit A 1 ^ N) := by
  let U := Units.mkOfMulEqOne (invOfUnit A 1) A (invOfUnit_mul A 1 hA)
  have h := DiagonalVanishingIndexDivisibility.power_coefficient_identity U (N : ℤ) j hj
  have hd : (N : ℤ) ∣ (j : ℤ) * coeff j (↑(U ^ (N : ℤ)) : PowerSeries ℤ) :=
    ⟨_, h⟩
  simpa [U] using hd

-- The affine difference converts index-weighted divisibility into exponent-weighted divisibility.
private theorem affine_summand_dvd (d n m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (b c : ℤ) (hb : ((d * (m - 1) + 1 : ℕ) : ℤ) ∣ b)
    (hc : ((d * (n - 1) + 1 : ℕ) : ℤ) ∣ (n - m : ℕ) * c) :
    ((d * (n - 1) + 1 : ℕ) : ℤ) ∣ b * c := by
  have haff : ((d * (m - 1) + 1 : ℕ) : ℤ) =
      ((d * (n - 1) + 1 : ℕ) : ℤ) - (d : ℤ) * (n - m : ℕ) := by
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_sub (by omega : m ≤ n)]
    push_cast
    ring
  obtain ⟨q, rfl⟩ := hb
  have he : ((d * (n - 1) + 1 : ℕ) : ℤ) ∣
      ((d * (m - 1) + 1 : ℕ) : ℤ) * c := by
    rw [haff, sub_mul, mul_assoc]
    exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right hc _)
  simpa only [mul_right_comm] using dvd_mul_of_dvd_left he q

theorem exponent_self_divisibility (d : ℕ) (_hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
    ((d * (n - 1) + 1 : ℕ) : ℤ) ∣ NegativePowerDiagonalModPrime.a (d + 1) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      simp
    have hn2 : 1 < n := by omega
    let A := NegativePowerDiagonalModPrime.generatingSeries (d + 1)
    have hA : constantCoeff A = 1 := by
      simpa only [coeff_zero_eq_constantCoeff] using
        (NegativePowerDiagonalModPrime.generating_equation (d + 1)).1
    have hrec := (NegativePowerDiagonalModPrime.generating_equation (d + 1)).2.2 n hn2
    simp only [Nat.add_sub_cancel] at hrec
    rw [coeff_diagonal] at hrec
    have heq : NegativePowerDiagonalModPrime.a (d + 1) n =
        -∑ m ∈ Finset.range n, coeff m A *
          coeff (n - m) (invOfUnit A 1 ^ ((d * (n - 1) + 1) * m)) := by
      simpa only [A, NegativePowerDiagonalModPrime.generatingSeries, coeff_mk] using
        eq_neg_of_add_eq_zero_left hrec
    rw [heq]
    apply dvd_neg.mpr
    apply Finset.dvd_sum
    intro m hm
    have hmn := Finset.mem_range.mp hm
    by_cases hm0 : m = 0
    · subst m
      simp [show n ≠ 0 by omega]
    have hc := inverse_power_dvd A hA ((d * (n - 1) + 1) * m) (n - m) (by omega)
    apply affine_summand_dvd d n m (by omega) hmn
    · simpa only [A, NegativePowerDiagonalModPrime.generatingSeries, coeff_mk] using
        ih m hmn (by omega)
    · have hdiv : ((d * (n - 1) + 1 : ℕ) : ℤ) ∣
          (((d * (n - 1) + 1) * m : ℕ) : ℤ) := by
        exact_mod_cast dvd_mul_right (d * (n - 1) + 1) m
      exact hdiv.trans hc

theorem hanna_conjecture_a395833 (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℤ) - 1) ∣ NegativePowerDiagonalModPrime.a 3 n := by
  have h := exponent_self_divisibility 2 (by omega) n hn
  convert h using 1
  push_cast
  omega

#print axioms exponent_self_divisibility
#print axioms hanna_conjecture_a395833

end D5.S1.Recurrence.Residue.DiagonalExponentSelfDivisibility
