/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairBalaDivisibility
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairBalaDivisibility
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: Bala's terminating identity for h_d and divisibility of h_d(m) by moduli coprime to (d-1)!. -/

import D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialColumnFamily
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Prime.Factorial

/-! Bala's terminating identity and divisibility for the binomial column family `h_d`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairBalaDivisibility

open PowerSeries Finset
open D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialColumnFamily

section

private theorem alt_gf (d : ℕ) : (1 + X : ℤ⟦X⟧) ^ d * rescale (-1) ((1 + X) * (invOneSubPow ℤ d).val) =
    1 - X := by
  have h1 : (1 - X : ℤ⟦X⟧) ^ d * (invOneSubPow ℤ d).val = 1 := by
    have := (invOneSubPow ℤ d).inv_val
    rwa [invOneSubPow_inv_eq_one_sub_pow] at this
  have h2 := congrArg (rescale (-1 : ℤ)) h1
  simp only [map_mul, map_pow, map_sub, map_one, rescale_neg_one_X, sub_neg_eq_add] at h2
  rw [map_mul, map_add, map_one, rescale_neg_one_X]
  calc (1 + X : ℤ⟦X⟧) ^ d * ((1 + -X) * rescale (-1) (invOneSubPow ℤ d).val)
      = (1 + -X) * ((1 + X) ^ d * rescale (-1) (invOneSubPow ℤ d).val) := by ring
    _ = 1 - X := by rw [h2]; ring

private theorem coeff_one_add_X_pow' (k j : ℕ) : coeff j ((1 + X : ℤ⟦X⟧) ^ k) = (k.choose j : ℤ) := by
  have : (1 + X : ℤ⟦X⟧) ^ k = (((1 + Polynomial.X) ^ k : Polynomial ℤ) : ℤ⟦X⟧) := by
    simp
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private theorem int_identity (d n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ range (n + 1), (-1) ^ j * h d j * ((2 * n + d - 1).choose (n - j) : ℤ) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have key : rescale (-1) ((1 + X) * (invOneSubPow ℤ d).val) * (1 + X : ℤ⟦X⟧) ^ (2 * (k + 1) + d - 1)
      = (1 + X) ^ (2 * k + 1) - X * (1 + X) ^ (2 * k + 1) := by
    rw [show 2 * (k + 1) + d - 1 = (2 * k + 1) + d by omega, pow_add,
      show ∀ a b c : ℤ⟦X⟧, a * (b * c) = b * (c * a) from fun a b c => by ring,
      alt_gf]
    ring
  have hc := congrArg (coeff (k + 1)) key
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (rescale (-1) ((1 + X) * (invOneSubPow ℤ d).val)) *
      coeff j ((1 + X : ℤ⟦X⟧) ^ (2 * (k + 1) + d - 1)))] at hc
  rw [map_sub, coeff_succ_X_mul, coeff_one_add_X_pow', coeff_one_add_X_pow',
    Nat.choose_symm_half, sub_self] at hc
  rw [← hc]
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_rescale, coeff_one_add_X_pow']
  simp [h]

private theorem term_eq (d n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    (∏ i ∈ range j, ((n : ℚ) - i)) / ∏ i ∈ range j, ((n : ℚ) + d + i) =
      ((2 * n + d - 1).choose (n - j) : ℚ) *
        ((n.factorial * (n + d - 1).factorial : ℚ) / (2 * n + d - 1).factorial) := by
  have hD : (∏ i ∈ range j, ((n : ℚ) - i)) * (n - j).factorial = n.factorial := by
    have : (∏ i ∈ range j, ((n : ℚ) - i)) = (n.descFactorial j : ℚ) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      refine prod_congr rfl fun i hi => ?_
      rw [Nat.cast_sub (by simp at hi; omega)]
    rw [this, mul_comm]; exact_mod_cast Nat.factorial_mul_descFactorial hj
  have hA : (∏ i ∈ range j, ((n : ℚ) + d + i)) * (n + d - 1).factorial =
      (n + d - 1 + j).factorial := by
    have : (∏ i ∈ range j, ((n : ℚ) + d + i)) = ((n + d - 1 + 1).ascFactorial j : ℚ) := by
      rw [Nat.ascFactorial_eq_prod_range, show n + d - 1 + 1 = n + d by omega]
      push_cast; rfl
    rw [this, mul_comm]; exact_mod_cast Nat.factorial_mul_ascFactorial (n + d - 1) j
  have hC : ((2 * n + d - 1).choose (n - j) : ℚ) * (n - j).factorial * (n + d - 1 + j).factorial =
      (2 * n + d - 1).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show n - j ≤ 2 * n + d - 1 by omega)
    rw [show 2 * n + d - 1 - (n - j) = n + d - 1 + j by omega] at this
    exact_mod_cast this
  have h1 : ((n - j).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n + d - 1).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((n + d - 1 + j).factorial : ℚ) ≠ 0 := by positivity
  have hP : (∏ i ∈ range j, ((n : ℚ) - i)) = n.factorial / (n - j).factorial :=
    eq_div_of_mul_eq h1 hD
  have hQ : (∏ i ∈ range j, ((n : ℚ) + d + i)) = (n + d - 1 + j).factorial / (n + d - 1).factorial :=
    eq_div_of_mul_eq h2 hA
  have h4 : ((2 * n + d - 1).choose (n - j) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show n - j ≤ 2 * n + d - 1 by omega)).ne'
  rw [hP, hQ, ← hC]
  field_simp

private theorem bala (d n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ range (n + 1), (-1 : ℚ) ^ j * h d j * (∏ i ∈ range j, ((n : ℚ) - i)) /
      ∏ i ∈ range j, ((n : ℚ) + d + i) = 0 := by
  have := congrArg (fun z : ℤ => (z : ℚ) *
    ((n.factorial * (n + d - 1).factorial : ℚ) / (2 * n + d - 1).factorial)) (int_identity d n hn)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    zero_mul, Int.cast_zero, sum_mul] at this
  rw [← this]
  refine sum_congr rfl fun j hj => ?_
  rw [mul_div_assoc, term_eq d n j hn (by simp at hj; omega)]
  ring

private theorem prod_formula (d m : ℕ) (hd : 2 ≤ d) :
    ((d - 1).factorial : ℤ) * h d m =
      ((2 * m + d - 1 : ℕ) : ℤ) * ∏ i ∈ range (d - 2), ((m + i + 1 : ℕ) : ℤ) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hq := ((result.1 (e + 2) m hd).2.2)
  have hasc := Nat.ascFactorial_eq_factorial_mul_choose m e
  rw [Nat.ascFactorial_eq_prod_range] at hasc
  simp only [show e + 2 - 1 = e + 1 by omega, show e + 2 - 2 = e by omega,
    show m + (e + 2) - 2 = m + e by omega] at hq ⊢
  rw [show ((e + 2 : ℕ) : ℚ) - 1 = (e : ℚ) + 1 by push_cast; ring] at hq
  have he : (e : ℚ) + 1 ≠ 0 := by positivity
  have hcast : ((∏ i ∈ range e, ((m + i + 1 : ℕ) : ℤ)) : ℚ) = (e.factorial : ℚ) * (m + e).choose e := by
    have := congrArg (fun z : ℕ => (z : ℚ)) hasc
    simp only [Nat.cast_prod, Nat.cast_mul] at this
    push_cast at this ⊢
    rw [← this]; refine prod_congr rfl fun i _ => by ring
  have : (((e + 1).factorial : ℤ) * h (e + 2) m : ℚ) =
      ((((2 * m + (e + 2) - 1 : ℕ) : ℤ) * ∏ i ∈ range e, ((m + i + 1 : ℕ) : ℤ) : ℤ) : ℚ) := by
    push_cast [Int.cast_prod] at hcast ⊢
    rw [hcast, hq, Nat.factorial_succ, show 2 * m + (e + 2) - 1 = 2 * m + e + 1 by omega]
    push_cast
    field_simp
    ring
  exact_mod_cast this

private theorem dvd_iff (d m q : ℕ) (hd : 2 ≤ d) (hq : Nat.Coprime q (d - 1).factorial) :
    (q : ℤ) ∣ h d m ↔
      (q : ℤ) ∣ ((2 * m + d - 1 : ℕ) : ℤ) * ∏ i ∈ range (d - 2), ((m + i + 1 : ℕ) : ℤ) := by
  rw [← prod_formula d m hd]
  refine ⟨fun hdvd => dvd_mul_of_dvd_right hdvd _, fun hdvd => ?_⟩
  rw [mul_comm] at hdvd
  exact (Nat.isCoprime_iff_coprime.2 hq).dvd_of_dvd_mul_right hdvd

private theorem dvd_of_coprime (d m q : ℕ) (hd : 2 ≤ d) (hq : Nat.Coprime q (d - 1).factorial)
    (hcase : (∃ j, 1 ≤ j ∧ j ≤ d - 2 ∧ q ∣ m + j) ∨ q ∣ 2 * m + d - 1) : (q : ℤ) ∣ h d m := by
  rw [dvd_iff d m q hd hq]
  rcases hcase with ⟨j, h1, h2, hj⟩ | h2
  · apply dvd_mul_of_dvd_right
    refine dvd_trans ?_ (dvd_prod_of_mem _ (mem_range.2 (show j - 1 < d - 2 by omega)))
    rw [show m + (j - 1) + 1 = m + j by omega]; exact_mod_cast hj
  · apply dvd_mul_of_dvd_left; exact_mod_cast h2

end

/-- Corollary 7 of the Ma–Zhang note on A208509, for `h_d(m) = [z^m](1 + z)/(1 - z)^d`:
Bala's terminating identity for every `d` and `n ≥ 1`; for `d ≥ 2` and `q` coprime to `(d - 1)!`,
`q ∣ h_d(m)` exactly when `q ∣ (2m + d - 1)(m + 1)⋯(m + d - 2)`; hence every such `q` that divides
`m + j` for some `1 ≤ j ≤ d - 2`, or `2m + d - 1`, divides `h_d(m)`, in particular every prime
power `p^e` with `p > d - 1`. -/
theorem result :
    (∀ d n : ℕ, 1 ≤ n →
      ∑ j ∈ range (n + 1), (-1 : ℚ) ^ j * h d j * (∏ i ∈ range j, ((n : ℚ) - i)) /
        ∏ i ∈ range j, ((n : ℚ) + d + i) = 0) ∧
    (∀ d m q : ℕ, 2 ≤ d → Nat.Coprime q (d - 1).factorial →
      ((q : ℤ) ∣ h d m ↔
        (q : ℤ) ∣ ((2 * m + d - 1 : ℕ) : ℤ) * ∏ i ∈ range (d - 2), ((m + i + 1 : ℕ) : ℤ))) ∧
    (∀ d m q : ℕ, 2 ≤ d → Nat.Coprime q (d - 1).factorial →
      ((∃ j, 1 ≤ j ∧ j ≤ d - 2 ∧ q ∣ m + j) ∨ q ∣ 2 * m + d - 1) → (q : ℤ) ∣ h d m) ∧
    (∀ d m p e : ℕ, 2 ≤ d → p.Prime → d - 1 < p →
      ((∃ j, 1 ≤ j ∧ j ≤ d - 2 ∧ p ^ e ∣ m + j) ∨ p ^ e ∣ 2 * m + d - 1) →
        ((p ^ e : ℕ) : ℤ) ∣ h d m) := by
  refine ⟨bala, dvd_iff, dvd_of_coprime, fun d m p e hd hp hlt hcase => dvd_of_coprime d m (p ^ e) hd ?_ hcase⟩
  refine Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_)
  have := (Nat.Prime.dvd_factorial hp).1 hdvd
  omega

end D5.S1.Recurrence.Invariants.AffinePolynomialPairBalaDivisibility
