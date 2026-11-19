/- GID: D5/S3/ArithSums/HannaLaurentDivisorFormula
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaLaurentDivisorFormula
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The A391810 Laurent coefficients are divisor sums of signed binomials. -/

import D5.S3.ArithSums.HannaLaurentRowSums
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.NumberTheory.Divisors

/-! # Divisor formula for the A391810 Laurent coefficients

For `n ≥ 1`, the coefficient `T(n,k)` of `x^(-k)` in the formal Laurent expansion of
`∑_{j ∈ ℤ} x^j (1 - x^j)^(n+j)` equals `-1` at `k = 0` and, for `k ≥ 1`, the sum over the
divisors `h ≤ n` of `k` of `(-1)^(k/h-1) C(n-h, k/h-1)`. The first five columns follow.
-/

namespace D5.S3.ArithSums.HannaLaurentDivisorFormula

open D5.S3.ArithSums.HannaLaurentRowSums
open Polynomial
open scoped BigOperators

private lemma coeff_one_sub_X_pow (m r : ℕ) :
    ((1 - X : ℤ[X]) ^ m).coeff r = (-1) ^ r * (m.choose r : ℤ) := by
  induction m generalizing r with
  | zero => rcases r with _ | r <;> simp [coeff_one]
  | succ m ih =>
    rw [pow_succ, mul_sub, mul_one, coeff_sub]
    rcases r with _ | r
    · simp [ih]
    · rw [coeff_mul_X, ih, ih, Nat.choose_succ_succ']
      push_cast
      ring

private lemma coeff_term (h m k : ℕ) (hh : 0 < h) :
    (X ^ h * (1 - X ^ h : ℤ[X]) ^ m).coeff k =
      if h ∣ k ∧ 0 < k then (-1) ^ (k / h - 1) * (m.choose (k / h - 1) : ℤ) else 0 := by
  have hexp : (1 - X ^ h : ℤ[X]) ^ m = expand ℤ h ((1 - X) ^ m) := by
    simp [map_pow, map_sub, expand_X]
  rw [coeff_X_pow_mul', hexp]
  by_cases hk : h ≤ k
  · simp only [hk, ↓reduceIte]
    rw [coeff_expand hh]
    by_cases hd : h ∣ k ∧ 0 < k
    · obtain ⟨⟨q, rfl⟩, hpos⟩ := hd
      have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
      have hsub : h * q - h = h * (q - 1) := by rw [Nat.mul_sub_one]
      have hdvd : h ∣ h * q - h := by rw [hsub]; exact dvd_mul_right h _
      simp only [hdvd, dvd_mul_right, hpos, and_self, ↓reduceIte]
      rw [hsub, Nat.mul_div_cancel_left _ hh, Nat.mul_div_cancel_left _ hh,
        coeff_one_sub_X_pow]
    · have hnd : ¬ h ∣ k - h := by
        intro hd'
        apply hd
        refine ⟨?_, by omega⟩
        have := Nat.dvd_add hd' (dvd_refl h)
        rwa [Nat.sub_add_cancel hk] at this
      simp only [hnd, hd, ↓reduceIte]
  · have hd : ¬ (h ∣ k ∧ 0 < k) := fun hd => hk (Nat.le_of_dvd hd.2 hd.1)
    simp only [hk, hd, ↓reduceIte]

private lemma row_coeff_zero (n : ℕ) : (rowPolynomial n).coeff 0 = -1 := by
  unfold rowPolynomial
  rw [coeff_add, finsetSum_coeff]
  simp

private lemma row_coeff (n k : ℕ) (hk : 0 < k) :
    (rowPolynomial n).coeff k =
      ∑ h ∈ (Nat.divisors k).filter (· ≤ n),
        (-1) ^ (k / h - 1) * ((n - h).choose (k / h - 1) : ℤ) := by
  unfold rowPolynomial
  rw [coeff_add, finsetSum_coeff]
  have hc : (-1 : ℤ[X]).coeff k = 0 := by
    rw [coeff_neg, coeff_one]
    simp [show k ≠ 0 by omega]
  rw [hc, zero_add,
    Finset.sum_congr rfl (fun j _ => coeff_term (j + 1) (n - (j + 1)) k (by omega)),
    Finset.range_eq_Ico, Finset.sum_Ico_add' (fun h =>
      if h ∣ k ∧ 0 < k then (-1) ^ (k / h - 1) * ((n - h).choose (k / h - 1) : ℤ) else 0),
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext h
  simp only [Finset.mem_filter, Finset.mem_Ico, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd, _⟩
    exact ⟨⟨hd, by omega⟩, by omega⟩
  · rintro ⟨⟨hd, _⟩, hn⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hk, by omega⟩, hd, hk⟩

/-- For `n ≥ 1`, the Laurent coefficient `T(n,k)` of `x^(-k)` is `-1` at `k = 0`, and for
`k ≥ 1` it is the sum over divisors `h ≤ n` of `k` of `(-1)^(k/h-1) C(n-h, k/h-1)`. In
particular `T(n,1) = 1`, `T(n,2) = -(n-2)`, `T(n,3) = n(n-3)/2 + 2` and
`T(n,4) = -(n-3)(n^2-3n+8)/6` in their stated ranges. -/
theorem divisor_formula (n : ℕ) (hn : 0 < n) :
    (series n hn).coeff 0 = -1 ∧
    (∀ k : ℕ, 0 < k → (series n hn).coeff (-(k : ℤ)) =
      ∑ h ∈ (Nat.divisors k).filter (· ≤ n),
        (-1 : ℚ) ^ (k / h - 1) * ((n - h).choose (k / h - 1) : ℚ)) ∧
    (series n hn).coeff (-1) = 1 ∧
    (2 ≤ n → (series n hn).coeff (-2) = -((n : ℚ) - 2)) ∧
    (3 ≤ n → (series n hn).coeff (-3) = (n : ℚ) * ((n : ℚ) - 3) / 2 + 2) ∧
    (4 ≤ n → (series n hn).coeff (-4) = -(((n : ℚ) - 3) * ((n : ℚ) ^ 2 - 3 * n + 8)) / 6) := by
  have hgen : ∀ k : ℕ, 0 < k → (series n hn).coeff (-(k : ℤ)) =
      ∑ h ∈ (Nat.divisors k).filter (· ≤ n),
        (-1 : ℚ) ^ (k / h - 1) * ((n - h).choose (k / h - 1) : ℚ) := by
    intro k hk
    rw [series_coefficient n hn k, row_coeff n k hk]
    push_cast
    rfl
  refine ⟨?_, hgen, ?_, ?_, ?_, ?_⟩
  · have := series_coefficient n hn 0
    simp only [Nat.cast_zero, neg_zero] at this
    rw [this, row_coeff_zero]
    norm_num
  · have := hgen 1 (by norm_num)
    rw [show Nat.divisors 1 = {1} from by decide,
      Finset.filter_true_of_mem (fun h hh => by simp at hh; omega)] at this
    push_cast at this
    rw [this]
    simp
  · intro h2
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have := hgen 2 (by norm_num)
    rw [show Nat.divisors 2 = {1, 2} from by decide,
      Finset.filter_true_of_mem (fun h hh => by simp at hh; omega),
      Finset.sum_insert (by decide), Finset.sum_singleton] at this
    push_cast at this
    rw [this]
    norm_num
  · intro h3
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := hgen 3 (by norm_num)
    rw [show Nat.divisors 3 = {1, 3} from by decide,
      Finset.filter_true_of_mem (fun h hh => by simp at hh; omega),
      Finset.sum_insert (by decide), Finset.sum_singleton] at this
    push_cast at this
    rw [this]
    norm_num
    rw [Nat.cast_choose_two]
    push_cast
    ring
  · intro h4
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := hgen 4 (by norm_num)
    rw [show Nat.divisors 4 = {1, 2, 4} from by decide,
      Finset.filter_true_of_mem (fun h hh => by simp at hh; omega),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at this
    push_cast at this
    rw [this]
    norm_num
    have s3 : ((m + 3).choose 3 : ℚ) * 3 = ((m : ℚ) + 3) * ((m + 2).choose 2 : ℚ) := by
      have hq : ((m + 2 + 1 : ℕ) : ℚ) * ((m + 2).choose 2 : ℚ) =
          ((m + 2 + 1).choose (2 + 1) : ℚ) * ((2 : ℕ) + 1 : ℚ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq (m + 2) 2
      push_cast at hq
      linarith
    have h2 : ((m + 2).choose 2 : ℚ) = ((m : ℚ) + 2) * ((m : ℚ) + 1) / 2 := by
      rw [Nat.cast_choose_two]
      push_cast
      ring
    have h3 : ((m + 3).choose 3 : ℚ) = ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) / 6 := by
      rw [h2] at s3
      linarith
    rw [h3]
    ring

end D5.S3.ArithSums.HannaLaurentDivisorFormula
