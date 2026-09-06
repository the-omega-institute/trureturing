/- GID: D5/S1/Recurrence/CentralFactorialParityIdentity
   generality: G
   mirror-B: D5/B/S1/Recurrence/CentralFactorialParityIdentity
   mirror-E: none(waiver:universal-symbolic-identities)
   anchors: []
   utility: none
   digest: Half-shift factorization proves two central-factorial coefficient identities. -/

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial Finset

namespace D5.S1.Recurrence.CentralFactorialParityIdentity

private noncomputable def squareProduct (n : ℕ) (a : ℚ) : Polynomial ℚ :=
  ∏ j ∈ range n, (X ^ 2 - Polynomial.C (((j : ℚ) + a) ^ 2))

/-- Signed rational coefficients of the even and odd central-factorial products. -/
noncomputable def centralFactorial (N K : ℕ) : ℚ :=
  if N % 2 = 0 then (squareProduct (N / 2) 0).coeff K
  else (X * squareProduct (N / 2) (1 / 2)).coeff K

/-- The integer-root odd polynomial. -/
noncomputable def A (n : ℕ) : Polynomial ℚ :=
  X * ∏ j ∈ Icc 1 (n - 1), (X ^ 2 - Polynomial.C ((j : ℚ) ^ 2))

/-- The half-integer-root even polynomial. -/
noncomputable def Cpoly (n : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Icc 1 (n - 1), (X ^ 2 - Polynomial.C (((j : ℚ) - 1 / 2) ^ 2))

/-- The half-integer-root product is unchanged by negating its argument. -/
theorem Cpoly_even (n : ℕ) : (Cpoly n).comp (0 - X) = Cpoly n := by
  simp [Cpoly, Polynomial.prod_comp]

private lemma prod_Icc_one (n : ℕ) (f : ℕ → Polynomial ℚ) :
    ∏ j ∈ Icc 1 n, f j = ∏ j ∈ range n, f (j + 1) := by
  rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel, add_comm 1]

private lemma A_eq_squareProduct (n : ℕ) : A n = X * squareProduct (n - 1) 1 := by
  simp only [A, prod_Icc_one, squareProduct, Nat.cast_add, Nat.cast_one]

private lemma Cpoly_eq_squareProduct (n : ℕ) :
    Cpoly n = squareProduct (n - 1) (1 / 2) := by
  simp only [Cpoly, prod_Icc_one, squareProduct, Nat.cast_add, Nat.cast_one]
  congr 1
  ext j
  congr 2
  ring

private lemma squareProduct_succ (n : ℕ) (a : ℚ) :
    squareProduct (n + 1) a = squareProduct n a *
      (X ^ 2 - Polynomial.C (((n : ℚ) + a) ^ 2)) := by
  simp only [squareProduct, prod_range_succ]

-- The new integer-root factor pairs with the preceding linear factor.
private lemma half_shift_aux (n : ℕ) :
    (X * squareProduct n 1).comp (X + Polynomial.C (1 / 2)) =
      (X + Polynomial.C ((n : ℚ) + 1 / 2)) * squareProduct n (1 / 2) := by
  induction n with
  | zero => simp [squareProduct]
  | succ n ih =>
    rw [squareProduct_succ, ← mul_assoc, mul_comp, ih, sub_comp, pow_comp,
      X_comp, C_comp, squareProduct_succ]
    simp only [Nat.cast_add, Nat.cast_one, Polynomial.C_add, Polynomial.C_pow,
      Polynomial.C_1]
    polynomial

/-- The universal half-shift factorization, proved by induction on the product length. -/
theorem half_shift (n : ℕ) (hn : 1 ≤ n) :
    (A n).comp (X + Polynomial.C (1 / 2)) =
      (X + Polynomial.C ((n : ℚ) - 1 / 2)) * Cpoly n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [A_eq_squareProduct, Cpoly_eq_squareProduct, Nat.succ_eq_add_one,
    Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_one, show (r : ℚ) + 1 - 1 / 2 = (r : ℚ) + 1 / 2 by ring]
    using half_shift_aux r

/-- Half the odd integer-root polynomial evaluated at `(1 + X) / 2`. -/
noncomputable def F (n : ℕ) : Polynomial ℚ :=
  Polynomial.C (1 / 2) * (A n).comp (Polynomial.C (1 / 2) * (1 + X))

/-- The scaled half-shift is a linear factor times an even polynomial. -/
theorem F_factorization (n : ℕ) (hn : 1 ≤ n) :
    F n = Polynomial.C (1 / 4) * (X + Polynomial.C (2 * (n : ℚ) - 1)) *
      (Cpoly n).comp (Polynomial.C (1 / 2) * X) := by
  have h := congrArg (fun p : Polynomial ℚ => p.comp (Polynomial.C (1 / 2) * X))
    (half_shift n hn)
  simp only [Polynomial.comp_assoc, add_comp, X_comp, C_comp, mul_comp] at h
  have hs : Polynomial.C (1 / 2 : ℚ) * X + Polynomial.C (1 / 2) =
      Polynomial.C (1 / 2) * (1 + X) := by ring
  rw [hs] at h
  rw [F, h]
  simp only [Polynomial.C_sub, Polynomial.C_mul]
  polynomial

private noncomputable def baseProduct (n : ℕ) (a : ℚ) : Polynomial ℚ :=
  ∏ j ∈ range n, (X - Polynomial.C (((j : ℚ) + a) ^ 2))

private lemma squareProduct_eq_expand (n : ℕ) (a : ℚ) :
    squareProduct n a = Polynomial.expand ℚ 2 (baseProduct n a) := by
  simp only [expand_eq_comp_X_pow, baseProduct, Polynomial.prod_comp, sub_comp,
    X_comp, C_comp, squareProduct]

private lemma baseProduct_degree (n : ℕ) (a : ℚ) :
    (baseProduct n a).natDegree ≤ n := by
  induction n with
  | zero => simp [baseProduct]
  | succ n ih =>
    rw [baseProduct, prod_range_succ]
    refine natDegree_mul_le.trans ?_
    rw [natDegree_X_sub_C]
    exact Nat.add_le_add_right ih 1

private lemma squareProduct_even_coeff (n k : ℕ) (a : ℚ) :
    (squareProduct n a).coeff (2 * k) = (baseProduct n a).coeff k := by
  rw [squareProduct_eq_expand, coeff_expand_mul' (by decide)]

private lemma squareProduct_odd_coeff (n k : ℕ) (a : ℚ) :
    (squareProduct n a).coeff (2 * k + 1) = 0 := by
  rw [squareProduct_eq_expand, coeff_expand (by decide)]
  simp

private lemma squareProduct_zero_succ (n : ℕ) :
    squareProduct (n + 1) 0 = X ^ 2 * squareProduct n 1 := by
  simp only [squareProduct, prod_range_succ', Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
    map_zero, sub_zero, Nat.cast_add, Nat.cast_one, add_zero]
  ring

private lemma centralFactorial_even (n k : ℕ) :
    centralFactorial (2 * (n + 1)) (2 * (k + 1)) = (baseProduct n 1).coeff k := by
  unfold centralFactorial
  rw [if_pos (by omega), Nat.mul_div_cancel_left _ (by decide : 0 < 2), squareProduct_zero_succ]
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, coeff_X_pow_mul, squareProduct_even_coeff]

private lemma centralFactorial_odd (n k : ℕ) :
    centralFactorial (2 * n + 1) (2 * k + 1) = (baseProduct n (1 / 2)).coeff k := by
  simp only [centralFactorial, Nat.add_mod, Nat.mul_mod_right, Nat.reduceMod,
    Nat.zero_add, Nat.one_ne_zero, if_false, Nat.mul_add_div (by decide : 0 < 2),
    Nat.reduceDiv, Nat.add_zero, coeff_X_mul, squareProduct_even_coeff]

private lemma F_odd_coeff (n k : ℕ) :
    (F (n + 1)).coeff (2 * k + 1) =
      (1 / 4 : ℚ) ^ (k + 1) * (baseProduct n (1 / 2)).coeff k := by
  rw [F_factorization _ (by omega)]
  rw [mul_assoc, add_mul, coeff_C_mul, coeff_add, coeff_X_mul, coeff_C_mul,
    comp_C_mul_X_coeff, comp_C_mul_X_coeff]
  simp only [Cpoly_eq_squareProduct, Nat.add_sub_cancel, squareProduct_even_coeff, squareProduct_odd_coeff,
    zero_mul, mul_zero, add_zero]
  rw [pow_mul]
  norm_num
  ring

private lemma scaled_monomial (q : ℕ) (e : ℚ) :
    Polynomial.C (1 / 2 : ℚ) *
      (Polynomial.C (1 / 2) * (1 + X) *
        (Polynomial.C e * ((Polynomial.C (1 / 2) * (1 + X)) ^ 2) ^ q)) =
      Polynomial.C ((1 / 4 : ℚ) ^ (q + 1) * e) * (1 + X) ^ (2 * q + 1) := by
  have h : (Polynomial.C (1 / 2 : ℚ) * (1 + X)) ^ 2 =
      Polynomial.C (1 / 4) * (1 + X) ^ 2 := by polynomial
  rw [h, mul_pow, ← Polynomial.C_pow]
  rw [← pow_mul]
  polynomial

private lemma F_coeff_sum (n l : ℕ) :
    (F (n + 1)).coeff l =
      ∑ q ∈ range (n + 1),
        (1 / 4 : ℚ) ^ (q + 1) * ((2 * q + 1).choose l : ℚ) * (baseProduct n 1).coeff q := by
  rw [F, A_eq_squareProduct, Nat.add_sub_cancel, squareProduct_eq_expand, expand_eq_comp_X_pow,
    mul_comp, X_comp, Polynomial.comp_assoc, pow_comp, X_comp]
  rw [Polynomial.comp, eval₂_eq_sum_range' Polynomial.C (Nat.lt_succ_of_le (baseProduct_degree n 1))]
  simp only [Finset.mul_sum, scaled_monomial, finsetSum_coeff, coeff_C_mul,
    coeff_one_add_X_pow]
  apply sum_congr rfl
  intro q hq
  ring

private lemma identity_427_core (n k : ℕ) :
    (1 / 4 : ℚ) ^ (k + 1) * centralFactorial (2 * n + 1) (2 * k + 1) =
      ∑ q ∈ range (n + 1),
        (1 / 4 : ℚ) ^ (q + 1) * ((2 * q + 1).choose (2 * k + 1) : ℚ) *
          centralFactorial (2 * (n + 1)) (2 * (q + 1)) := by
  simp only [centralFactorial_even, centralFactorial_odd]
  rw [← F_odd_coeff, F_coeff_sum]

private lemma sum_Icc_one (n : ℕ) (f : ℕ → ℚ) :
    ∑ q ∈ Icc 1 (n + 1), f q = ∑ q ∈ range (n + 1), f (q + 1) := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm 1]

/-- The full parity identity for every positive `n` and `k`, including empty sums. -/
theorem identity_427 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (1 / 4 : ℚ) ^ k * centralFactorial (2 * n - 1) (2 * k - 1) =
      ∑ q ∈ Icc k n, (1 / 4 : ℚ) ^ q * ((2 * q - 1).choose (2 * k - 1) : ℚ) *
        centralFactorial (2 * n) (2 * q) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_eq_add_one] at *
  have h := identity_427_core r s
  rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega,
    show 2 * (s + 1) - 1 = 2 * s + 1 by omega]
  rw [h]
  let f : ℕ → ℚ := fun q => (1 / 4 : ℚ) ^ q *
    ((2 * q - 1).choose (2 * s + 1) : ℚ) * centralFactorial (2 * (r + 1)) (2 * q)
  have hs : ∑ q ∈ Icc 1 (r + 1), f q =
      ∑ q ∈ range (r + 1), (1 / 4 : ℚ) ^ (q + 1) *
        ((2 * q + 1).choose (2 * s + 1) : ℚ) *
          centralFactorial (2 * (r + 1)) (2 * (q + 1)) := by
    rw [sum_Icc_one]
    apply sum_congr rfl
    intro q hq
    simp only [f, show 2 * (q + 1) - 1 = 2 * q + 1 by omega]
  rw [← hs]
  change ∑ q ∈ Icc 1 (r + 1), f q = ∑ q ∈ Icc (s + 1) (r + 1), f q
  symm
  apply sum_subset
  · intro q hq
    simp only [mem_Icc] at *
    omega
  · intro q hq hnot
    have hqk : q < s + 1 := by simp only [mem_Icc] at *; omega
    have hz : (2 * q - 1).choose (2 * s + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [f, hz, Nat.cast_zero, mul_zero, zero_mul]

/-- Every even coefficient of `F n` is `2*n-1` times the next odd coefficient. -/
theorem adjacent_coefficients (n r : ℕ) (hn : 1 ≤ n) :
    (F n).coeff (2 * r) = (2 * (n : ℚ) - 1) * (F n).coeff (2 * r + 1) := by
  rw [F_factorization n hn]
  simp only [mul_assoc, add_mul, coeff_C_mul, coeff_add]
  have ho : ((Cpoly n).comp (Polynomial.C (1 / 2) * X)).coeff (2 * r + 1) = 0 := by
    simp only [comp_C_mul_X_coeff, Cpoly_eq_squareProduct, squareProduct_odd_coeff, zero_mul]
  rw [coeff_X_mul, ho, mul_zero, add_zero]
  have he : (X * (Cpoly n).comp (Polynomial.C (1 / 2) * X)).coeff (2 * r) = 0 := by
    cases r with
    | zero => simp
    | succ r =>
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, coeff_X_mul]
      simp only [comp_C_mul_X_coeff, Cpoly_eq_squareProduct, squareProduct_odd_coeff, zero_mul]
  rw [he, zero_add]
  ring

private lemma F_coeff_sum_reflected (n l : ℕ) :
    (F (n + 1)).coeff l =
      ∑ k ∈ range (n + 1), (1 / 4 : ℚ) ^ (n - k + 1) *
        ((2 * (n - k) + 1).choose l : ℚ) * (baseProduct n 1).coeff (n - k) := by
  rw [F_coeff_sum, ← sum_range_reflect]
  simp only [Nat.add_sub_cancel]

private lemma F_coeff_sum_truncated (n m l : ℕ) (hm : m ≤ n) (hl : 2 * (n - m) ≤ l) :
    (F (n + 1)).coeff l =
      ∑ k ∈ range (m + 1), (1 / 4 : ℚ) ^ (n - k + 1) *
        ((2 * (n - k) + 1).choose l : ℚ) * (baseProduct n 1).coeff (n - k) := by
  rw [F_coeff_sum_reflected]
  symm
  apply sum_subset (range_mono (by omega))
  intro k hk hnot
  have hz : (2 * (n - k) + 1).choose l = 0 := by
    apply Nat.choose_eq_zero_of_lt
    simp only [mem_range] at *
    omega
  simp only [hz, Nat.cast_zero, mul_zero, zero_mul]

private lemma F_odd_sum_truncated (n m : ℕ) (hm : m ≤ n) :
    (F (n + 1)).coeff (2 * (n - m) + 1) =
      ∑ k ∈ range (m + 1), (1 / 4 : ℚ) ^ (n - k + 1) *
        ((2 * (n - k) + 1).choose (2 * (n - m) + 1) : ℚ) *
          (baseProduct n 1).coeff (n - k) := by
  have h := identity_427 (n + 1) (n - m + 1) (by omega) (by omega)
  simp only [show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
    show 2 * (n - m + 1) - 1 = 2 * (n - m) + 1 by omega,
    centralFactorial_odd] at h
  rw [← F_odd_coeff] at h
  rw [h]
  symm
  apply sum_bij (fun k _ => n - k + 1)
  · intro k hk
    simp only [mem_Icc, mem_range] at *
    omega
  · intro k hk j hj heq
    simp only [mem_range] at *
    omega
  · intro q hq
    refine ⟨n + 1 - q, ?_, ?_⟩ <;> simp only [mem_Icc, mem_range] at * <;> omega
  · intro k hk
    simp only [centralFactorial_even,
      show 2 * (n - k + 1) - 1 = 2 * (n - k) + 1 by omega]

/-- The adjacent-binomial relation over the rational coefficient field. -/
theorem choose_adjacent (p d : ℕ) :
    ((p + 1 : ℕ) : ℚ) * (p.choose d : ℚ) =
      ((p.choose d : ℚ) + (p.choose (d + 1) : ℚ)) * ((d + 1 : ℕ) : ℚ) := by
  have h := Nat.add_one_mul_choose_eq p d
  rw [Nat.choose_succ_succ'] at h
  exact_mod_cast h

private lemma choose_weight (n m k : ℕ) (hm : m ≤ n) (hk : k ≤ m) :
    ((2 * (n - k) + 1).choose (2 * (n - m)) : ℚ) *
        ((2 * (n + 1) * (m - k) + k : ℕ) : ℚ) =
      ((2 * (n - m) + 1 : ℕ) : ℚ) / 2 *
        ((2 * (n : ℚ) + 1) * ((2 * (n - k) + 1).choose (2 * (n - m) + 1) : ℚ) -
          ((2 * (n - k) + 1).choose (2 * (n - m)) : ℚ)) := by
  have h := choose_adjacent (2 * (n - k) + 1) (2 * (n - m))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_sub hm, Nat.cast_sub (hk.trans hm), Nat.cast_sub hk] at h ⊢
  linear_combination (2 * (n : ℚ) + 1) / 2 * h

private lemma pow_four_cancel (n k : ℕ) (hk : k ≤ n) :
    (4 : ℚ) ^ (n + 1) * (1 / 4 : ℚ) ^ (n - k + 1) = (4 : ℚ) ^ k := by
  calc
    _ = (4 : ℚ) ^ (k + (n - k + 1)) * (1 / 4 : ℚ) ^ (n - k + 1) := by
      congr 2
      omega
    _ = (4 : ℚ) ^ k := by rw [pow_add, mul_assoc, ← mul_pow]; norm_num

private lemma weighted_sum_reduction_core (n m : ℕ) (hm : m ≤ n) :
    ∑ k ∈ range (m + 1), (4 : ℚ) ^ k * (baseProduct n 1).coeff (n - k) *
      ((2 * (n - k) + 1).choose (2 * (n - m)) : ℚ) *
        ((2 * (n + 1) * (m - k) + k : ℕ) : ℚ) =
      (4 : ℚ) ^ (n + 1) * (2 * (n - m) + 1 : ℕ) / 2 *
        ((2 * (n : ℚ) + 1) * (F (n + 1)).coeff (2 * (n - m) + 1) -
          (F (n + 1)).coeff (2 * (n - m))) := by
  let d := 2 * (n - m)
  have hsum :
      ∑ k ∈ range (m + 1), (4 : ℚ) ^ k * (baseProduct n 1).coeff (n - k) *
        ((2 * (n - k) + 1).choose d : ℚ) *
          ((2 * (n + 1) * (m - k) + k : ℕ) : ℚ) =
      (4 : ℚ) ^ (n + 1) * (d + 1 : ℕ) / 2 *
        ((2 * (n : ℚ) + 1) * (F (n + 1)).coeff (d + 1) - (F (n + 1)).coeff d) := by
    rw [F_odd_sum_truncated n m hm,
      F_coeff_sum_truncated n m d hm (by omega)]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    have hkm : k ≤ m := by simpa only [mem_range, Nat.lt_succ_iff] using hk
    have hc := choose_weight n m k hm hkm
    have hp := pow_four_cancel n k (hkm.trans hm)
    dsimp [d] at *
    calc
      _ = (4 : ℚ) ^ k * (baseProduct n 1).coeff (n - k) *
          (((2 * (n - k) + 1 : ℕ).choose (2 * (n - m)) : ℚ) *
            ((2 * (n + 1) * (m - k) + k : ℕ) : ℚ)) := by ring
      _ = _ := by rw [hc, ← hp]; ring
  exact hsum

private lemma identity_441_core (n m : ℕ) (hm : m ≤ n) :
    ∑ k ∈ range (m + 1), (4 : ℚ) ^ k * (baseProduct n 1).coeff (n - k) *
      ((2 * (n - k) + 1).choose (2 * (n - m)) : ℚ) *
        ((2 * (n + 1) * (m - k) + k : ℕ) : ℚ) = 0 := by
  have h := adjacent_coefficients (n + 1) (n - m) (by omega)
  rw [weighted_sum_reduction_core n m hm]
  have hh : (2 * (n : ℚ) + 1) * (F (n + 1)).coeff (2 * (n - m) + 1) -
      (F (n + 1)).coeff (2 * (n - m)) = 0 := by
    rw [h]
    push_cast
    ring
  rw [hh, mul_zero]

/-- The weighted sum reduces to the adjacent-coefficient difference of `F n`. -/
theorem weighted_sum_reduction (n m : ℕ) (hn : 1 ≤ n) (hm : m ≤ n - 1) :
    ∑ k ∈ range (m + 1), (4 : ℚ) ^ k * centralFactorial (2 * n) (2 * (n - k)) *
      ((2 * (n - k) - 1).choose (2 * (n - m - 1)) : ℚ) *
        ((2 * n * (m - k) + k : ℕ) : ℚ) =
      (4 : ℚ) ^ n * ((2 * (n - m - 1) + 1 : ℕ) : ℚ) / 2 *
        ((2 * (n : ℚ) - 1) * (F n).coeff (2 * (n - m - 1) + 1) -
          (F n).coeff (2 * (n - m - 1))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
  rw [show r + 1 - m - 1 = r - m by omega]
  have hs : (2 * ((r + 1 : ℕ) : ℚ) - 1) = 2 * (r : ℚ) + 1 := by
    push_cast
    ring
  rw [hs, ← weighted_sum_reduction_core r m hm]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  have hkr : k ≤ r := hkm.trans hm
  rw [show r + 1 - k = (r - k) + 1 by omega, centralFactorial_even,
    show 2 * (r - k + 1) - 1 = 2 * (r - k) + 1 by omega]

/-- The full weighted vanishing identity for every positive `n` and `m <= n-1`. -/
theorem identity_441 (n m : ℕ) (hn : 1 ≤ n) (hm : m ≤ n - 1) :
    ∑ k ∈ range (m + 1), (4 : ℚ) ^ k * centralFactorial (2 * n) (2 * (n - k)) *
      ((2 * (n - k) - 1).choose (2 * (n - m - 1)) : ℚ) *
        ((2 * n * (m - k) + k : ℕ) : ℚ) = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
  rw [← identity_441_core r m hm]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  have hkr : k ≤ r := hkm.trans hm
  rw [show r + 1 - k = (r - k) + 1 by omega, centralFactorial_even,
    show 2 * (r - k + 1) - 1 = 2 * (r - k) + 1 by omega,
    show r + 1 - m - 1 = r - m by omega]

example : centralFactorial 4 2 = -1 := by
  norm_num [centralFactorial, squareProduct, prod_range_succ, Polynomial.C_pow,
    Polynomial.C_1, mul_sub, sub_mul, coeff_sub, ← pow_add]

example : centralFactorial 6 4 = -5 := by
  norm_num [centralFactorial, squareProduct, prod_range_succ, Polynomial.C_pow,
    Polynomial.C_1, mul_sub, sub_mul, coeff_sub, ← pow_add]

example : centralFactorial 3 1 = -(1 / 4 : ℚ) := by
  change centralFactorial (2 * 1 + 1) (2 * 0 + 1) = -(1 / 4 : ℚ)
  rw [centralFactorial_odd]
  norm_num only [baseProduct, prod_range_one, Nat.cast_zero, zero_add, coeff_sub,
    coeff_X_zero, coeff_C_zero]

example : centralFactorial 5 1 = (9 / 16 : ℚ) := by
  change centralFactorial (2 * 2 + 1) (2 * 0 + 1) = (9 / 16 : ℚ)
  rw [centralFactorial_odd]
  norm_num only [baseProduct, prod_range_succ, prod_range_zero, one_mul,
    Nat.cast_zero, Nat.cast_one, zero_add, mul_coeff_zero, coeff_sub, coeff_X_zero,
    coeff_C_zero]

example : centralFactorial 5 3 = -(5 / 2 : ℚ) := by
  change centralFactorial (2 * 2 + 1) (2 * 1 + 1) = -(5 / 2 : ℚ)
  rw [centralFactorial_odd]
  norm_num only [baseProduct, prod_range_succ, prod_range_zero, one_mul, Nat.cast_one,
    Nat.cast_zero, zero_add, mul_sub, sub_mul, coeff_sub, coeff_X_mul, coeff_mul_C,
    coeff_X_zero, coeff_C_succ, coeff_C_zero, coeff_X_one, coeff_C_mul]

example : Nonempty (Polynomial ℚ) := ⟨X⟩

example : ∃ n k : ℕ, 1 ≤ n ∧ 1 ≤ k := ⟨1, 1, by decide, by decide⟩

example : ∃ n m : ℕ, 1 ≤ n ∧ m ≤ n - 1 := ⟨1, 0, by decide, by decide⟩

example (k : ℕ) : (1 / 4 : ℚ) ^ k = (4 : ℚ) ^ (-(k : ℤ)) := by
  simp only [zpow_neg, zpow_natCast, one_div, inv_pow]

#print axioms centralFactorial
#print axioms A
#print axioms Cpoly
#print axioms Cpoly_even
#print axioms half_shift
#print axioms F
#print axioms F_factorization
#print axioms adjacent_coefficients
#print axioms identity_427
#print axioms identity_441
#print axioms choose_adjacent
#print axioms weighted_sum_reduction

end D5.S1.Recurrence.CentralFactorialParityIdentity
