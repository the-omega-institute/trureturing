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
`n` into the parts `1, ell, …, ell ^ (r - 1)`.
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

end

end D5.S1.Digit.DigitCapPowerGF
