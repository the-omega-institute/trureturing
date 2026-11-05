/- GID: D5/S1/Digit/KurkovLowerBitRecurrence
   generality: G
   mirror-B: D5/B/S1/Digit/KurkovLowerBitRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The full lower-bit recurrence for the native binary-weight product sequence. -/

import D5.S1.Digit.KurkovWeightProductBinomial
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Binary prefix products and the complete lower-bit sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Digit.KurkovLowerBitRecurrence
open D5.S1.Digit.KurkovWeightProductBinomial (a)
open D5.S1.Digit.DyadicRowPolynomialRecurrence (wt wt_zero wt_even wt_odd)

private theorem weight_step (m : ℕ) : wt m = wt (m / 2) + m % 2 := by
  have h : m % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with he | ho
  · have hm : m = 2 * (m / 2) := by omega
    conv_lhs => rw [hm, wt_even]
    omega
  · have hm : m = 2 * (m / 2) + 1 := by omega
    conv_lhs => rw [hm, wt_odd]
    omega

private theorem bit_shift (m k : ℕ) :
    m / 2 ^ (k + 1) % 2 = (m / 2) / 2 ^ k % 2 := by
  rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (2 ^ k)]

private theorem add_pow_div (m k : ℕ) :
    (m + 2 ^ (k + 1)) / 2 = m / 2 + 2 ^ k := by
  rw [pow_succ]
  omega

private theorem add_pow_mod (m k : ℕ) :
    (m + 2 ^ (k + 1)) % 2 = m % 2 := by
  rw [pow_succ, Nat.add_mod]
  simp

private theorem weight_set (k m : ℕ) (h : m / 2 ^ k % 2 = 0) :
    wt (m + 2 ^ k) = wt m + 1 := by
  induction k generalizing m with
  | zero =>
    simp only [pow_zero, Nat.div_one] at h ⊢
    have hm : m = 2 * (m / 2) := by omega
    conv_lhs => rw [hm, wt_odd]
    conv_rhs => rw [hm, wt_even]
  | succ k ih =>
    rw [bit_shift] at h
    rw [weight_step (m + _), add_pow_div, add_pow_mod, ih _ h, weight_step m]
    omega

private def P : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | L + 1, c, m => (c + wt m) * P L c (m / 2)

private def Z : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | L + 1, c, m =>
    (if m % 2 = 0 then (c + 1 + wt (m / 2)) * P L c (m / 2) else 0) +
      (c + 1 + wt m) * Z L c (m / 2)

private theorem half_bound {L m : ℕ} (h : m < 2 ^ (L + 1)) :
    m / 2 < 2 ^ L := by
  rw [pow_succ] at h
  omega

private theorem product_identity (L c m : ℕ) (h : m < 2 ^ L) :
    (c + 1) * P L (c + 1) m = (c + 1 + wt m) * P L c m + Z L c m := by
  induction L generalizing m with
  | zero =>
    have hm : m = 0 := by simpa using h
    subst m
    simp [P, Z, wt_zero]
  | succ L ih =>
    have hi := ih (m / 2) (half_bound h)
    have hw := weight_step m
    have hb := Nat.mod_lt m (by decide : 0 < 2)
    by_cases he : m % 2 = 0
    · simp only [P, Z, if_pos he]
      have hw' : wt m = wt (m / 2) := by omega
      rw [hw']
      nlinarith only [congrArg (fun x => (c + 1 + wt (m / 2)) * x) hi]
    · have ho : m % 2 = 1 := by omega
      simp only [P, Z, if_neg he, zero_add]
      have hw' : wt m = wt (m / 2) + 1 := by omega
      rw [hw']
      nlinarith only [congrArg (fun x => (c + 2 + wt (m / 2)) * x) hi]

private theorem zero_sum (L c m : ℕ) :
    Z L c m = ∑ k ∈ Finset.range L,
      if m / 2 ^ k % 2 = 0 then P L c (m + 2 ^ k) else 0 := by
  induction L generalizing m with
  | zero => simp [Z]
  | succ L ih =>
    rw [Finset.sum_range_succ', Z, ih]
    have hs : (∑ k ∈ Finset.range L,
        if m / 2 ^ (k + 1) % 2 = 0 then P (L + 1) c (m + 2 ^ (k + 1)) else 0) =
        (c + 1 + wt m) * (∑ k ∈ Finset.range L,
        if (m / 2) / 2 ^ k % 2 = 0 then P L c (m / 2 + 2 ^ k) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [bit_shift]
      split_ifs with hb
      · have hw := weight_set (k + 1) m (by rwa [bit_shift])
        rw [P, hw, add_pow_div]
        congr 1; omega
      · simp
    rw [hs]
    simp only [pow_zero, Nat.div_one]
    by_cases he : m % 2 = 0
    · simp only [if_pos he, P]
      have hd : (m + 1) / 2 = m / 2 := by omega
      have hw : wt (m + 1) = wt (m / 2) + 1 := by
        have hm : m + 1 = 2 * (m / 2) + 1 := by omega
        rw [hm, wt_odd]
      rw [hd, hw]
      ring
    · simp [he]

private theorem bit_sum (L m : ℕ) (h : m < 2 ^ L) :
    (∑ k ∈ Finset.range L, m / 2 ^ k % 2) = wt m := by
  induction L generalizing m with
  | zero =>
    have hm : m = 0 := by simpa using h
    simp [hm, wt_zero]
  | succ L ih =>
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.div_one]
    simp_rw [bit_shift]
    rw [ih _ (half_bound h), weight_step m]

private theorem native_product (L m : ℕ) (h : m < 2 ^ L) : a m = P L 1 m := by
  induction L generalizing m with
  | zero =>
    have hm : m = 0 := by simpa using h
    simp [hm, a, P]
  | succ L ih =>
    rw [P, ← ih _ (half_bound h)]
    cases m with
    | zero => simp [a, wt_zero]
    | succ m => rw [a]

private theorem set_bound (L m k : ℕ) (h : m < 2 ^ L) (hk : k < L)
    (hb : m / 2 ^ k % 2 = 0) : m + 2 ^ k < 2 ^ L := by
  induction L generalizing m k with
  | zero => omega
  | succ L ih =>
    cases k with
    | zero =>
      simp only [pow_zero, Nat.div_one] at hb ⊢
      rw [pow_succ] at h ⊢
      omega
    | succ k =>
      have hi := ih (m / 2) k (half_bound h) (by omega) (by rwa [bit_shift] at hb)
      have hd := add_pow_div m k
      rw [pow_succ]
      omega

private theorem full_product_identity (L c m : ℕ) (h : m < 2 ^ L) :
    (c + 1) * P L (c + 1) m = (c + 1) * P L c m +
      ∑ k ∈ Finset.range L, P L c (m + 2 ^ k * (1 - m / 2 ^ k % 2)) := by
  have hs : (∑ k ∈ Finset.range L, P L c (m + 2 ^ k * (1 - m / 2 ^ k % 2))) =
      Z L c m + wt m * P L c m := by
    rw [zero_sum, ← bit_sum L m h, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hb := Nat.mod_lt (m / 2 ^ k) (by decide : 0 < 2)
    by_cases he : m / 2 ^ k % 2 = 0
    · simp [he]
    · have ho : m / 2 ^ k % 2 = 1 := by omega
      simp [ho]
  rw [hs, product_identity L c m h]
  ring

private theorem leading_weight (L m : ℕ) (h : m < 2 ^ L) :
    wt (2 ^ L + m) = wt m + 1 := by
  simpa only [Nat.add_comm] using weight_set L m (by simp [Nat.div_eq_of_lt h])

private theorem sequence_step (m : ℕ) : a m = (1 + wt m) * a (m / 2) := by
  cases m with
  | zero => simp [a, wt_zero]
  | succ m => rw [a]

private theorem native_initial : a 0 = 1 ∧ a 1 = 2 := by
  constructor
  · rw [a]
  · rw [sequence_step 1]
    have hw : wt 1 = 1 := by simpa [wt_zero] using wt_odd 0
    norm_num [hw, a]

private theorem leading_product (L m : ℕ) (h : m < 2 ^ L) :
    a (2 ^ L + m) = 2 * P L 2 m := by
  induction L generalizing m with
  | zero =>
    have hm : m = 0 := by simpa using h
    subst m
    simp only [pow_zero, Nat.add_zero, P, Nat.mul_one]
    exact native_initial.2
  | succ L ih =>
    rw [sequence_step, leading_weight _ _ h]
    have hd : (2 ^ (L + 1) + m) / 2 = 2 ^ L + m / 2 := by
      rw [pow_succ]
      omega
    rw [hd, ih _ (half_bound h), P]
    ring

private theorem dyadic_result (L m : ℕ) (h : m < 2 ^ L) :
    a (2 ^ L + m) = 2 * a m +
      ∑ k ∈ Finset.range L, a (m + 2 ^ k * (1 - m / 2 ^ k % 2)) := by
  rw [leading_product _ _ h, native_product _ _ h]
  have hi := full_product_identity L 1 m h
  simp only [Nat.reduceAdd] at hi
  rw [hi]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply (native_product L _ _).symm
  have hkl : k < L := Finset.mem_range.mp hk
  by_cases he : m / 2 ^ k % 2 = 0
  · simpa [he] using set_bound L m k h hkl he
  · have ho : m / 2 ^ k % 2 = 1 := by
      have hb := Nat.mod_lt (m / 2 ^ k) (by decide : 0 < 2)
      omega
    simpa [ho] using h

private theorem lower_bit (L m k : ℕ) (hk : k < L) :
    (2 ^ L + m) / 2 ^ k % 2 = m / 2 ^ k % 2 := by
  have he : L = k + (L - k - 1) + 1 := by omega
  have hp : 2 ^ L = (2 * 2 ^ (L - k - 1)) * 2 ^ k := by
    conv_lhs => rw [he, pow_succ, pow_add]
    ring
  rw [hp, Nat.mul_comm (2 * 2 ^ (L - k - 1)), Nat.mul_add_div (by positivity)]
  omega

/-- Kurkov's complete lower-bit recurrence, with the literal n-based bit. -/
private theorem lower_recurrence (n : ℕ) (hn : 1 < n) :
    a n = 2 * a (n - 2 ^ Nat.log 2 n) +
      ∑ k ∈ Finset.range (Nat.log 2 n),
        a (n - 2 ^ Nat.log 2 n + 2 ^ k * (1 - n / 2 ^ k % 2)) := by
  let L := Nat.log 2 n
  let m := n - 2 ^ L
  have hlo : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hm : m < 2 ^ L := by dsimp [m]; rw [pow_succ] at hhi; omega
  have he : n = 2 ^ L + m := by dsimp [m]; omega
  change a n = 2 * a m + ∑ k ∈ Finset.range L,
    a (m + 2 ^ k * (1 - n / 2 ^ k % 2))
  conv_lhs => rw [he]
  rw [dyadic_result L m hm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [he, lower_bit L m k (Finset.mem_range.mp hk)]

/-- Initial data, the defining recurrence, and the complete original-domain identity. -/
theorem result :
    a 0 = 1 ∧ a 1 = 2 ∧
    (∀ n : ℕ, 1 < n → a n = (1 + wt n) * a (n / 2)) ∧
    (∀ n : ℕ, 1 < n →
      a n = 2 * a (n - 2 ^ Nat.log 2 n) +
        ∑ k ∈ Finset.range (Nat.log 2 n),
          a (n - 2 ^ Nat.log 2 n + 2 ^ k * (1 - n / 2 ^ k % 2))) := by
  exact ⟨native_initial.1, native_initial.2, fun n _ => sequence_step n, lower_recurrence⟩

#print axioms result
end D5.S1.Digit.KurkovLowerBitRecurrence
