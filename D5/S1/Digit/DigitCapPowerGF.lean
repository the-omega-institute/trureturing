/- GID: D5/S1/Digit/DigitCapPowerGF
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapPowerGF
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Counts with digit cap ell^r-1 have generating function prod_{j<r} 1/(1-z^(ell^j)). -/

import D5.S1.Digit.DigitCapMultipleCount
import Mathlib.RingTheory.PowerSeries.Expand

/-! # Generating function of the counts with digit cap `ell ^ r - 1`

For a radix `ell ≥ 2` and `r ≥ 0`, the generating function of `b(ell ^ r - 1, ell, n)` times
`∏_{j < r} (1 - z ^ (ell ^ j))` is `1`; equivalently, the counts are the numbers of partitions of
`n` into the parts `1, ell, …, ell ^ (r - 1)`. The counts with cap `ell ^ (r + 1) - 1` lie
between `C(⌊n / ell ^ r⌋ + r, r)` and `(n + 1) ^ r`, hence are `Θ(n ^ r)`.
-/

set_option autoImplicit false

namespace D5.S1.Digit.DigitCapPowerGF

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open D5.S1.Digit.DigitCapMultipleCount
open PowerSeries

noncomputable section

/-- The generating function `∑ b(ell ^ r - 1, ell, n) z ^ n` over the integers. -/
def gf (ell r : ℕ) : PowerSeries ℤ := PowerSeries.mk fun n => (count (ell ^ r - 1) ell n : ℤ)

/-- The product `∏_{j < r} (1 - z ^ (ell ^ j))`. -/
def den (ell r : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.range r, (1 - X ^ (ell ^ j))

/-- With digit cap `0` only the empty representation exists. -/
private lemma count_cap_zero (ell n : ℕ) : count 0 ell n = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨0, by simp, by simp [weight]⟩, fun a => ?_⟩
    apply Subtype.ext
    ext i
    have := a.property.1 i
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  · apply Nat.card_eq_zero.mpr
    left
    constructor
    intro a
    have h0 : a.val = 0 := by
      ext i
      have := a.property.1 i
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    have := a.property.2
    rw [h0] at this
    simp [weight] at this
    exact hn this.symm

private lemma gf_zero (ell : ℕ) : gf ell 0 = 1 := by
  ext n
  simp only [gf, coeff_mk, pow_zero, Nat.sub_self, count_cap_zero, coeff_one]
  split_ifs <;> simp

/-- Differencing the multiple-cap identity: `(1 - z) G_{r+1} = G_r(z ^ ell)`. -/
private lemma gf_succ {ell : ℕ} (hell : 2 ≤ ell) (r : ℕ) :
    (1 - X) * gf ell (r + 1) = expand ell (by omega) (gf ell r) := by
  have hpow : ell ^ (r + 1) - 1 = ell ^ r * ell - 1 := by rw [pow_succ]
  have hc : ∀ n, count (ell ^ (r + 1) - 1) ell n =
      ∑ t ∈ Finset.range (n / ell + 1), count (ell ^ r - 1) ell t := by
    intro n
    rw [hpow, count_multiple ell (ell ^ r) n hell (Nat.one_le_pow _ _ (by omega))]
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_expand]
  rcases n with _ | n
  · simp [gf, coeff_mk, hc, Nat.zero_div]
  · rw [show X * gf ell (r + 1) = X * gf ell (r + 1) from rfl, coeff_succ_X_mul]
    simp only [gf, coeff_mk, hc]
    have hdiv : (n + 1) / ell = n / ell + if ell ∣ n + 1 then 1 else 0 := by
      split_ifs with h
      · rw [Nat.succ_div_of_dvd h]
      · rw [Nat.succ_div_of_not_dvd h, add_zero]
    split_ifs with h
    · simp only [h, ↓reduceIte] at hdiv
      rw [hdiv, Finset.sum_range_succ (n := n / ell + 1)]
      push_cast
      ring
    · simp only [h, ↓reduceIte, add_zero] at hdiv
      rw [hdiv]
      ring

private lemma den_succ {ell : ℕ} (hell : 2 ≤ ell) (r : ℕ) :
    den ell (r + 1) = (1 - X) * expand ell (by omega) (den ell r) := by
  unfold den
  rw [Finset.prod_range_succ', pow_zero, pow_one, map_prod, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [map_sub, map_one, map_pow, expand_X, ← pow_mul, pow_succ, mul_comm (ell ^ j)]

/-- For a radix `ell ≥ 2` and every `r`, `∏_{j < r} (1 - z ^ (ell ^ j)) · ∑ b(ell^r - 1, ell, n) z^n
= 1`, so the generating function is `∏_{j < r} (1 - z ^ (ell ^ j))⁻¹`. -/
theorem den_mul_gf (ell r : ℕ) (hell : 2 ≤ ell) : den ell r * gf ell r = 1 := by
  induction r with
  | zero => simp [den, gf_zero]
  | succ r ih =>
    rw [den_succ hell, mul_comm (1 - X), mul_assoc, gf_succ hell, ← map_mul, ih, map_one]

private lemma count_rec {ell : ℕ} (hell : 2 ≤ ell) (r n : ℕ) :
    count (ell ^ (r + 1) - 1) ell n =
      ∑ t ∈ Finset.range (n / ell + 1), count (ell ^ r - 1) ell t := by
  rw [show ell ^ (r + 1) - 1 = ell ^ r * ell - 1 by rw [pow_succ],
    count_multiple ell (ell ^ r) n hell (Nat.one_le_pow _ _ (by omega))]

private lemma count_one {ell : ℕ} (hell : 2 ≤ ell) (n : ℕ) : count (ell ^ 1 - 1) ell n = 1 := by
  rw [count_rec hell 0 n]
  simp only [pow_zero, Nat.sub_self, count_cap_zero]
  rw [Finset.sum_ite_eq' (Finset.range (n / ell + 1)) 0 (fun _ => 1)]
  simp

/-- Explicit growth: for `ell ≥ 2` and every `r`,
`C(⌊n / ell ^ r⌋ + r, r) ≤ b(ell ^ (r+1) - 1, ell, n) ≤ (n + 1) ^ r`, so the counts with digit
cap `ell ^ (r+1) - 1` grow like `n ^ r`. -/
theorem count_bounds (ell r n : ℕ) (hell : 2 ≤ ell) :
    (n / ell ^ r + r).choose r ≤ count (ell ^ (r + 1) - 1) ell n ∧
    count (ell ^ (r + 1) - 1) ell n ≤ (n + 1) ^ r := by
  induction r generalizing n with
  | zero =>
    have h := count_one hell n
    simp only [pow_one] at h
    simp [h]
  | succ r ih =>
    rw [count_rec hell (r + 1) n]
    constructor
    · have hS : n / ell ^ (r + 1) = n / ell / ell ^ r := by
        rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
      rw [hS, show n / ell / ell ^ r + (r + 1) = n / ell / ell ^ r + r + 1 by ring,
        ← Nat.sum_range_add_choose]
      have hinj : Set.InjOn (fun s => s * ell ^ r) (Finset.range (n / ell / ell ^ r + 1)) := by
        intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_right (by positivity) h
      calc ∑ i ∈ Finset.range (n / ell / ell ^ r + 1), (i + r).choose r
          = ∑ i ∈ Finset.range (n / ell / ell ^ r + 1), ((i * ell ^ r) / ell ^ r + r).choose r := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Nat.mul_div_cancel _ (by positivity)]
        _ = ∑ t ∈ (Finset.range (n / ell / ell ^ r + 1)).image (fun s => s * ell ^ r),
              (t / ell ^ r + r).choose r := by
            rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
        _ ≤ ∑ t ∈ Finset.range (n / ell + 1), (t / ell ^ r + r).choose r := by
            apply Finset.sum_le_sum_of_subset
            intro t ht
            obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
            simp only [Finset.mem_range] at hs ⊢
            have := Nat.div_mul_le_self (n / ell) (ell ^ r)
            have : s * ell ^ r ≤ n / ell / ell ^ r * ell ^ r :=
              Nat.mul_le_mul_right _ (by omega)
            omega
        _ ≤ ∑ t ∈ Finset.range (n / ell + 1), count (ell ^ (r + 1) - 1) ell t :=
            Finset.sum_le_sum fun t _ => (ih t).1
    · calc ∑ t ∈ Finset.range (n / ell + 1), count (ell ^ (r + 1) - 1) ell t
          ≤ ∑ t ∈ Finset.range (n / ell + 1), (n + 1) ^ r := by
            apply Finset.sum_le_sum
            intro t ht
            have ht' : t ≤ n := by
              have := Finset.mem_range.mp ht
              have := Nat.div_le_self n ell
              omega
            exact le_trans (ih t).2 (Nat.pow_le_pow_left (by omega) r)
        _ = (n / ell + 1) * (n + 1) ^ r := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        _ ≤ (n + 1) * (n + 1) ^ r :=
            Nat.mul_le_mul_right _ (by have := Nat.div_le_self n ell; omega)
        _ = (n + 1) ^ (r + 1) := by ring

/-- The counts with digit cap `ell ^ (r+1) - 1` are `Θ(n ^ r)`. -/
theorem count_isTheta (ell r : ℕ) (hell : 2 ≤ ell) :
    (fun n : ℕ => (count (ell ^ (r + 1) - 1) ell n : ℝ)) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound ((2 : ℝ) ^ r)
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h := (count_bounds ell r n hell).2
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_natCast, norm_pow, Real.norm_natCast, ← mul_pow]
    calc (count (ell ^ (r + 1) - 1) ell n : ℝ) ≤ ((n : ℝ) + 1) ^ r := by exact_mod_cast h
      _ ≤ (2 * (n : ℝ)) ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
  · apply Asymptotics.IsBigO.of_bound (((ell : ℝ) ^ r) ^ r * (r.factorial : ℝ))
    filter_upwards with n
    obtain ⟨m, hm⟩ : ∃ m, m = n / ell ^ r := ⟨_, rfl⟩
    have h := (count_bounds ell r n hell).1
    rw [← hm] at h
    have hc := Nat.pow_le_choose (α := ℝ) r (m + r)
    rw [show m + r + 1 - r = m + 1 by omega] at hc
    have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    have hc' : ((m : ℝ) + 1) ^ r ≤ (r.factorial : ℝ) * ((m + r).choose r : ℝ) := by
      have := (div_le_iff₀ hf).mp hc
      push_cast at this
      linarith
    have hn : (n : ℝ) ≤ (ell : ℝ) ^ r * ((m : ℝ) + 1) := by
      have h1 := Nat.lt_mul_div_succ n (show 0 < ell ^ r by positivity)
      rw [← hm] at h1
      have : n ≤ ell ^ r * (m + 1) := by omega
      exact_mod_cast this
    have hcount : ((m + r).choose r : ℝ) ≤ (count (ell ^ (r + 1) - 1) ell n : ℝ) := by
      exact_mod_cast h
    rw [Real.norm_natCast, norm_pow, Real.norm_natCast]
    calc (n : ℝ) ^ r ≤ ((ell : ℝ) ^ r * ((m : ℝ) + 1)) ^ r :=
          pow_le_pow_left₀ (by positivity) hn r
      _ = ((ell : ℝ) ^ r) ^ r * ((m : ℝ) + 1) ^ r := mul_pow _ _ _
      _ ≤ ((ell : ℝ) ^ r) ^ r * ((r.factorial : ℝ) * ((m + r).choose r : ℝ)) :=
          mul_le_mul_of_nonneg_left hc' (by positivity)
      _ ≤ ((ell : ℝ) ^ r) ^ r * ((r.factorial : ℝ) * (count (ell ^ (r + 1) - 1) ell n : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount hf.le) (by positivity)
      _ = ((ell : ℝ) ^ r) ^ r * (r.factorial : ℝ) * (count (ell ^ (r + 1) - 1) ell n : ℝ) := by
          ring

end

end D5.S1.Digit.DigitCapPowerGF
