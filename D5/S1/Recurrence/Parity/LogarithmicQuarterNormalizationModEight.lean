/- GID: D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral logarithmic normalization determines Hanna's coefficients modulo eight. -/

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.LinearCombination

open PowerSeries Finset

namespace D5.S1.Recurrence.Parity.LogarithmicQuarterNormalizationModEight

private def weight (n : ℕ) (z : ℤ) : ℤ :=
  if n = 1 then 1 else (4 * (n : ℤ) ^ 2 - 1) * z

/-- Integral normalization of the coefficients, with zero values below index two. -/
noncomputable def c (n : ℕ) : ℤ :=
  if hn : 2 ≤ n then
    weight (n - 1) (c (n - 1)) + 4 * ∑ k ∈ range n,
      if _hk : 2 ≤ k ∧ k < n then
        (k : ℤ) * c k * weight (n - k) (c (n - k)) else 0
  else 0
termination_by n
decreasing_by all_goals omega

/-- The sequence indexed from one; the unused constant coefficient is zero. -/
noncomputable def a (n : ℕ) : ℤ := weight n (c n)

private theorem c_small (n : ℕ) (hn : n < 2) : c n = 0 := by
  rw [c, dif_neg (by omega)]

private theorem a_zero : a 0 = 0 := by simp [a, weight, c_small]
private theorem a_one : a 1 = 1 := by simp [a, weight]

theorem c_recurrence (n : ℕ) (hn : 2 ≤ n) :
    c n = a (n - 1) + 4 * ∑ k ∈ Ico 2 n, (k : ℤ) * c k * a (n - k) := by
  rw [c, dif_pos hn]
  congr 1
  congr 1
  simp only [dite_eq_ite]
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_Ico]
  omega

theorem a_eq (n : ℕ) (hn : 2 ≤ n) : a n = (4 * (n : ℤ) ^ 2 - 1) * c n := by
  simp [a, weight, show n ≠ 1 by omega]

/-- The argument of the formal logarithm, in its integral normalization. -/
noncomputable def H : PowerSeries ℤ :=
  mk (fun n => if n = 0 then 1 else if n = 1 then 1 else 4 * (n : ℤ) * c n)

/-- The ordinary series associated to the logarithmic generating function. -/
noncomputable def B : PowerSeries ℤ := mk a

private theorem coeff_H (n : ℕ) (hn : 2 ≤ n) : coeff n H = 4 * (n : ℤ) * c n := by
  simp [H, show n ≠ 0 by omega, show n ≠ 1 by omega]

private theorem coeff_B (n : ℕ) : coeff n B = a n := coeff_mk _ _

private theorem convolution (n : ℕ) (hn : 2 ≤ n) :
    coeff n (B * H) = a n + a (n - 1) +
      4 * ∑ k ∈ Ico 2 n, (k : ℤ) * c k * a (n - k) := by
  rw [mul_comm B H, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i H * coeff j B) n]
  rw [sum_range_succ]
  simp only [coeff_B, Nat.sub_self, a_zero, mul_zero, add_zero]
  rw [← sum_range_add_sum_Ico _ (by omega : 2 ≤ n)]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.sub_zero]
  simp only [H, coeff_mk, ite_true, zero_ne_one, one_ne_zero, ite_false, one_mul]
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hk2 := (mem_Ico.mp hk).1
  simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, ite_false]
  ring

/-- The formal reading of L = log H is B H = X H', with H(0) = 1.
Here L has coefficient a(n)/n for n positive. -/
theorem log_derivative_identity : B * H = X * derivative ℤ H := by
  ext n
  rcases n with _ | n
  · simp [B, H, a_zero]
  by_cases hn : n + 1 = 1
  · have : n = 0 := by omega
    subst n
    rw [coeff_succ_X_mul, coeff_derivative, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i B * coeff j H) 1]
    simp [sum_range_succ, B, H, a_zero, a_one]
  · rw [convolution (n + 1) (by omega), coeff_succ_X_mul, coeff_derivative,
      coeff_H (n + 1) (by omega), add_assoc, ← c_recurrence (n + 1) (by omega),
      a_eq (n + 1) (by omega)]
    push_cast
    ring

theorem coeff_H_rat (n : ℕ) (hn : 2 ≤ n) :
    coeff n (H.map (Int.castRingHom ℚ)) =
      (4 * n : ℚ) / (4 * (n : ℚ) ^ 2 - 1) * (a n : ℚ) := by
  rw [coeff_map, coeff_H n hn, a_eq n hn]
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hd : 4 * (n : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  change ((4 * (n : ℤ) * c n : ℤ) : ℚ) = _
  push_cast
  field_simp

private theorem rational_identity :
    mk (fun n => (a n : ℚ)) * H.map (Int.castRingHom ℚ) =
      X * derivative ℚ (H.map (Int.castRingHom ℚ)) := by
  have hb : B.map (Int.castRingHom ℚ) = mk (fun n => (a n : ℚ)) := by
    ext n
    simp [B]
  have hd : (derivative ℤ H).map (Int.castRingHom ℚ) =
      derivative ℚ (H.map (Int.castRingHom ℚ)) := by
    ext n
    simp [coeff_derivative]
  have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) log_derivative_identity
  simpa only [map_mul, map_X, hb, hd] using he

private theorem convolution_split (b : ℕ → ℚ) (h : PowerSeries ℚ)
    (hb : b 0 = 0) (hh : coeff 0 h = 1) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (mk b * h) = b n + ∑ k ∈ Ico 1 n, coeff k h * b (n - k) := by
  rw [mul_comm (mk b) h, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i h * coeff j (mk b)) n, sum_range_succ]
  simp only [coeff_mk, Nat.sub_self, hb, mul_zero, add_zero]
  rw [← sum_range_add_sum_Ico _ hn]
  simp [hh]

/-- Uniqueness among rational coefficient sequences with the exact OEIS shape. -/
theorem generating_unique (b : ℕ → ℚ) (h : PowerSeries ℚ)
    (hb0 : b 0 = 0) (hb1 : b 1 = 1)
    (hh0 : coeff 0 h = 1) (hh1 : coeff 1 h = 1)
    (hshape : ∀ n : ℕ, 2 ≤ n → coeff n h =
      (4 * n : ℚ) / (4 * (n : ℚ) ^ 2 - 1) * b n)
    (heq : mk b * h = X * derivative ℚ h) :
    ∀ n : ℕ, b n = (a n : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [hb0, a_zero]
    by_cases hn1 : n = 1
    · subst n
      simp [hb1, a_one]
    have hn2 : 2 ≤ n := by omega
    have hprev : ∀ k < n, coeff k h = coeff k (H.map (Int.castRingHom ℚ)) := by
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simp [hh0, H]
      by_cases hk1 : k = 1
      · subst k
        simp [hh1, H]
      rw [hshape k (by omega), coeff_H_rat k (by omega), ih k hk]
    have hs : (∑ k ∈ Ico 1 n, coeff k h * b (n - k)) =
        ∑ k ∈ Ico 1 n, coeff k (H.map (Int.castRingHom ℚ)) * (a (n - k) : ℚ) := by
      apply sum_congr rfl
      intro k hk
      obtain ⟨hk1, hkn⟩ := mem_Ico.mp hk
      rw [hprev k hkn, ih (n - k) (by omega)]
    have hleft := congrArg (coeff n) heq
    have hright := congrArg (coeff n) rational_identity
    rw [convolution_split b h hb0 hh0 n (by omega)] at hleft
    rw [convolution_split (fun n => (a n : ℚ)) _
      (by simp [a_zero]) (by simp [H]) n (by omega)] at hright
    have hx (f : PowerSeries ℚ) : coeff n (X * derivative ℚ f) =
        coeff n f * (n : ℚ) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      simp [coeff_succ_X_mul, coeff_derivative]
    rw [hx, hshape n hn2, hs] at hleft
    rw [hx, coeff_H_rat n hn2] at hright
    have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    have hd : 4 * (n : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hdiff : b n - (a n : ℚ) =
        ((4 * n : ℚ) / (4 * (n : ℚ) ^ 2 - 1) * (b n - (a n : ℚ))) * n := by
      linear_combination hleft - hright
    field_simp at hdiff
    nlinarith

private theorem odd_pair (n : ℕ) (hn : 1 ≤ n) :
    a n % 2 = 1 ∧ (2 ≤ n → c n % 2 = 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 1
    · subst n
      simp [a_one]
    have hn2 : 2 ≤ n := by omega
    have hp := (ih (n - 1) (by omega) (by omega)).1
    have hc : c n % 2 = 1 := by
      have hr := c_recurrence n hn2
      omega
    constructor
    · rw [a_eq n hn2, Int.mul_emod, hc]
      norm_num [Int.sub_emod, Int.mul_emod]
    · exact fun _ => hc

theorem all_odd (n : ℕ) (hn : 1 ≤ n) : Odd (a n) :=
  Int.odd_iff.mpr (odd_pair n hn).1

private theorem four_sum_indices (n : ℕ) (hn : 2 ≤ n) :
    (4 * ∑ k ∈ Ico 2 n, (k : ℤ)) % 8 =
      if n % 4 = 0 ∨ n % 4 = 1 then 4 else 0 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn, mul_add, Int.add_emod, ih]
    have hcast : (n : ℤ) % 4 = (n % 4 : ℕ) := by omega
    have hm : (4 * (n : ℤ)) % 8 = 4 * ((n : ℤ) % 2) := by omega
    rw [hm]
    split_ifs <;> omega

private theorem normalized_mod_eight (n : ℕ) (hn : 2 ≤ n) :
    c n % 8 = (a (n - 1) + if n % 4 = 0 ∨ n % 4 = 1 then 4 else 0) % 8 := by
  have hs : (∑ k ∈ Ico 2 n, (k : ℤ) * c k * a (n - k)) % 2 =
      (∑ k ∈ Ico 2 n, (k : ℤ)) % 2 := by
    apply Int.ModEq.sum
    intro k hk
    obtain ⟨hk2, hkn⟩ := mem_Ico.mp hk
    change _ % 2 = _ % 2
    simp [Int.mul_emod, (odd_pair k (by omega)).2 hk2,
      (odd_pair (n - k) (by omega)).1]
  have hfour := four_sum_indices n hn
  have hr := c_recurrence n hn
  omega

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) :
    (n % 4 = 1 → a n % 8 = 1) ∧ (n % 4 = 2 → a n % 8 = 7) ∧
    (n % 4 = 3 → a n % 8 = 5) ∧ (n % 4 = 0 → a n % 8 = 7) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 1
    · subst n
      norm_num [a_one]
    have hn2 : 2 ≤ n := by omega
    have hp := ih (n - 1) (by omega) (by omega)
    have hc := normalized_mod_eight n hn2
    have heq := a_eq n hn2
    have ha : a n % 8 = (((4 * (n : ℤ) ^ 2 - 1) % 8) * (c n % 8)) % 8 := by
      rw [heq, Int.mul_emod]
    have hfactor : (4 * (n : ℤ) ^ 2 - 1) % 8 =
        if n % 2 = 0 then 7 else 3 := by
      have hpow : (n : ℤ) ^ 2 % 2 = (n : ℤ) % 2 := by
        rw [pow_two, Int.mul_emod]
        have : (n : ℤ) % 2 = 0 ∨ (n : ℤ) % 2 = 1 := by omega
        rcases this with h | h <;> rw [h] <;> norm_num
      split_ifs <;> omega
    rw [hfactor] at ha
    have hnmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hnmod with h | h | h | h <;>
      simp only [show n % 2 = n % 4 % 2 by omega, h] at ha hc <;>
      norm_num at ha hc <;> omega

#print axioms c_recurrence
#print axioms a_eq
#print axioms log_derivative_identity
#print axioms coeff_H_rat
#print axioms generating_unique
#print axioms all_odd
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.LogarithmicQuarterNormalizationModEight
