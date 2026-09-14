/- GID: D5/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Normalized positive polynomial exponents divide their diagonal coefficients. -/

import D5.S1.Recurrence.Residue.DiagonalExponentSelfDivisibility
import Mathlib.Algebra.Polynomial.Div

/-!
Library-search audit (offline, pinned checkout):
* D5: `polynomial_exponent_self`, `exponent_self_divisibility`, and
  `fun m => m ^ k`: no polynomial theorem; the affine theorem is narrower.
* D5 and Mathlib/Algebra/Polynomial/Div.lean: `sub_dvd_eval_sub` hits
  `Polynomial.sub_dvd_eval_sub`, also used in CubicOddBisection; applied below.
* D5: `coeff_diagonal` and `inverse_power_dvd` are private. Their local
  adapters use Mathlib's `coeff_subst'` and the frozen public
  `DiagonalVanishingIndexDivisibility.power_coefficient_identity`.
* Mathlib/Data/Int: `natCast_toNat` locates the nonnegative coercion API.
* The frozen `index_power_divisibility` already yields the monomial
  conclusion by `dvd_rfl`; `hanna_conjecture_a292394` is its square instance.

For an integer polynomial P positive on positive integers and P(1) = 1,
use the normalized series with natural exponent `(P.eval n).toNat`.
The nonnegative coercion identity preserves these exponent values.
Polynomial divided differences transfer index-weighted coefficient
identities to exponent divisibility, which propagates by strong induction.
The value P(1) = 1 supplies the base case; no condition at zero is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open PowerSeries
namespace D5.S1.Recurrence.Residue.PolynomialExponentSelfDivisibility

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

private theorem eval_toNat_cast (P : Polynomial ℤ)
    (hpos : ∀ m : ℕ, 1 ≤ m → 1 ≤ P.eval (m : ℤ))
    (m : ℕ) (hm : 1 ≤ m) :
    ((P.eval (m : ℤ)).toNat : ℤ) = P.eval (m : ℤ) := by
  exact Int.toNat_of_nonneg (le_trans (by decide : (0 : ℤ) ≤ 1) (hpos m hm))

private theorem polynomial_summand_dvd (P : Polynomial ℤ) (n m : ℕ)
    (hmn : m < n) (b c : ℤ) (hb : P.eval (m : ℤ) ∣ b)
    (hc : P.eval (n : ℤ) ∣ (n - m : ℕ) * c) :
    P.eval (n : ℤ) ∣ b * c := by
  have hdiff : ((n - m : ℕ) : ℤ) ∣ P.eval (n : ℤ) - P.eval (m : ℤ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hmn)]
    exact Polynomial.sub_dvd_eval_sub (n : ℤ) (m : ℤ) P
  obtain ⟨q, hq⟩ := hdiff
  obtain ⟨r, rfl⟩ := hb
  have he : P.eval (n : ℤ) ∣ P.eval (m : ℤ) * c := by
    have hm : P.eval (m : ℤ) = P.eval (n : ℤ) - q * (n - m : ℕ) := by
      linear_combination -hq
    rw [hm, sub_mul, mul_assoc]
    exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right hc _)
  simpa only [mul_right_comm] using dvd_mul_of_dvd_left he r

/-- Positive integer polynomial exponents normalized at one divide their own
coefficients in the normalized vanishing-diagonal construction. -/
theorem polynomial_exponent_self_divisibility
    (P : Polynomial ℤ) (hP : P.eval 1 = 1)
    (hpos : ∀ n : ℕ, 1 ≤ n → 1 ≤ P.eval (n : ℤ))
    (n : ℕ) (hn : 1 ≤ n) :
    P.eval (n : ℤ) ∣ DiagonalVanishingIndexDivisibility.a
      (fun m => (P.eval (m : ℤ)).toNat) n := by
  let e : ℕ → ℕ := fun m => (P.eval (m : ℤ)).toNat
  change P.eval (n : ℤ) ∣ DiagonalVanishingIndexDivisibility.a e n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      simp [hP]
    have hn2 : 1 < n := by omega
    let A := DiagonalVanishingIndexDivisibility.generatingSeries e
    have hA : constantCoeff A = 1 := by
      simpa only [coeff_zero_eq_constantCoeff] using
        (DiagonalVanishingIndexDivisibility.generating_equation e).1
    have hrec := (DiagonalVanishingIndexDivisibility.generating_equation e).2.2 n hn2
    rw [coeff_diagonal] at hrec
    have heq : DiagonalVanishingIndexDivisibility.a e n =
        -∑ m ∈ Finset.range n, coeff m A *
          coeff (n - m) (invOfUnit A 1 ^ (e n * m)) := by
      simpa only [A, DiagonalVanishingIndexDivisibility.generatingSeries, coeff_mk] using
        eq_neg_of_add_eq_zero_left hrec
    rw [heq]
    apply dvd_neg.mpr
    apply Finset.dvd_sum
    intro m hm
    have hmn := Finset.mem_range.mp hm
    by_cases hm0 : m = 0
    · subst m
      simp [show n ≠ 0 by omega]
    have hc := inverse_power_dvd A hA (e n * m) (n - m) (by omega)
    apply polynomial_summand_dvd P n m hmn
    · simpa only [A, DiagonalVanishingIndexDivisibility.generatingSeries, coeff_mk] using
        ih m hmn (by omega)
    · have hdiv : P.eval (n : ℤ) ∣ ((e n * m : ℕ) : ℤ) := by
        rw [Nat.cast_mul, show (e n : ℤ) = P.eval (n : ℤ) from eval_toNat_cast P hpos n hn]
        exact dvd_mul_right _ _
      exact hdiv.trans hc

private theorem affine_eval (d m : ℕ) (hm : 1 ≤ m) :
    (Polynomial.C (d : ℤ) * (Polynomial.X - 1) + 1).eval (m : ℤ) =
      ((d * (m - 1) + 1 : ℕ) : ℤ) := by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hm]
  simp

-- Equality follows from uniqueness, not definitional equality: at m = 0
-- the polynomial's truncated exponent can differ from d * (m - 1) + 1.
private theorem affine_polynomial_agreement (d n : ℕ) :
    DiagonalVanishingIndexDivisibility.a
      (fun m => ((Polynomial.C (d : ℤ) * (Polynomial.X - 1) + 1).eval (m : ℤ)).toNat) n =
      NegativePowerDiagonalModPrime.a (d + 1) n := by
  let e : ℕ → ℕ := fun m =>
    ((Polynomial.C (d : ℤ) * (Polynomial.X - 1) + 1).eval (m : ℤ)).toNat
  have h := DiagonalVanishingIndexDivisibility.generating_equation e
  have he : DiagonalVanishingIndexDivisibility.generatingSeries e =
      NegativePowerDiagonalModPrime.generatingSeries (d + 1) := by
    apply NegativePowerDiagonalModPrime.generating_unique (d + 1) _ h.1 h.2.1
    intro m hm
    have hexp : e m = ((d + 1) - 1) * (m - 1) + 1 := by
      change ((Polynomial.C (d : ℤ) * (Polynomial.X - 1) + 1).eval (m : ℤ)).toNat = _
      rw [affine_eval d m (by omega)]
      simp only [Int.toNat_natCast, Nat.add_sub_cancel]
    simpa only [hexp] using h.2.2 m hm
  simpa only [DiagonalVanishingIndexDivisibility.generatingSeries,
    NegativePowerDiagonalModPrime.generatingSeries, coeff_mk] using congrArg (coeff n) he

/-- The instance P = C d * (X - 1) + 1 agrees coefficientwise with the frozen
series at parameter d + 1, by generating-series uniqueness. For n ≥ 1 its
value is the natural affine exponent d * (n - 1) + 1, recovering
`DiagonalExponentSelfDivisibility.exponent_self_divisibility`.
The proof also allows d = 0. -/
theorem affine_polynomial_exponent_self_divisibility (d n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.C (d : ℤ) * (Polynomial.X - 1) + 1).eval (n : ℤ) ∣
      NegativePowerDiagonalModPrime.a (d + 1) n := by
  rw [← affine_polynomial_agreement d n]
  apply polynomial_exponent_self_divisibility
  · simp
  · intro m hm
    rw [affine_eval d m hm]
    exact_mod_cast (Nat.le_add_left 1 (d * (m - 1)))
  · exact hn

/-- The instance P = X^k yields divisibility by the entire exponent.
This is not the statement of `index_power_divisibility`, whose hypothesis
specifies an index power dividing an arbitrary exponent. The monomial
conclusion is also its direct instance (use `dvd_rfl`); the square case is
already `hanna_conjecture_a292394`. No subsumption of the general theorems
is asserted. -/
theorem monomial_exponent_self_divisibility (k n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ^ k ∣ DiagonalVanishingIndexDivisibility.a (fun m => m ^ k) n := by
  have h := polynomial_exponent_self_divisibility (Polynomial.X ^ k)
    (by simp) (by
      intro m hm
      simpa using (one_le_pow₀ (show (1 : ℤ) ≤ m by exact_mod_cast hm))) n hn
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, ← Nat.cast_pow,
    Int.toNat_natCast] using h

#print axioms polynomial_exponent_self_divisibility
#print axioms affine_polynomial_exponent_self_divisibility
#print axioms monomial_exponent_self_divisibility

end D5.S1.Recurrence.Residue.PolynomialExponentSelfDivisibility
