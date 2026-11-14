/- GID: D5/S3/Constants/Moments/A117187MatharRecurrence
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/A117187MatharRecurrence
   mirror-E: none(waiver:formal-power-series-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: The literal A117187 generating function satisfies Mathar's order-three recurrence. -/

import D5.S3.Constants.Moments.A331474HankelBridge
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse

/-! The source denominator is interpreted by its normalized root and unit inverse. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open PowerSeries
namespace D5.S3.Constants.Moments.A117187MatharRecurrence

private abbrev Provider := D5.S3.Constants.Moments.A331474HankelBridge.b

/-- The standard Catalan series with x replaced by x squared. -/
def catalan_square : PowerSeries ℤ :=
  expand 2 (by decide) D5.S3.Constants.Moments.A331474HankelBridge.catalanInt

/-- The constant-one square-root branch of 1-4x². -/
def source_root : PowerSeries ℤ := 1 - 2 * X ^ 2 * catalan_square

/-- The entire denominator printed in the source generating function. -/
def denominator : PowerSeries ℤ := (1 - X ^ 2 * catalan_square) * source_root

/-- The literal source generating function, using the constant-one unit inverse. -/
def source_series : PowerSeries ℤ :=
  (1 + X) * catalan_square * invOfUnit denominator 1

/-- Offset-zero coefficients of the literal source generating function. -/
def a (n : ℕ) : ℤ := coeff n source_series

private theorem catalan_equation :
    X ^ 2 * catalan_square ^ 2 + 1 = catalan_square := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  have h' := congrArg (expand 2 (by decide) : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ) h
  simpa [catalan_square, D5.S3.Constants.Moments.A331474HankelBridge.catalanInt,
    mul_comm, expand_X] using h'

private theorem root_spec :
    constantCoeff source_root = 1 ∧ source_root ^ 2 = 1 - 4 * X ^ 2 ∧
    ∀ r : PowerSeries ℤ, constantCoeff r = 1 → r ^ 2 = 1 - 4 * X ^ 2 →
      r = source_root := by
  have hs : source_root ^ 2 = 1 - 4 * X ^ 2 := by
    dsimp [source_root]
    linear_combination 4 * X ^ 2 * catalan_equation
  have hc : constantCoeff source_root = 1 := by simp [source_root]
  refine ⟨hc, hs, ?_⟩
  intro r hr hsq
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hsq.trans hs.symm) with h | h
  · exact h
  · have he := congrArg (constantCoeff (R := ℤ)) h
    simp only [map_neg, hr, hc] at he
    norm_num at he

private theorem denominator_inverse :
    IsUnit denominator ∧
    denominator * invOfUnit denominator 1 = 1 ∧
    invOfUnit denominator 1 * denominator = 1 := by
  have hc : constantCoeff denominator = (1 : ℤˣ) := by
    simp [denominator, root_spec.1]
  exact ⟨isUnit_iff_constantCoeff.mpr (by rw [hc]; exact isUnit_one),
    mul_invOfUnit _ _ hc, invOfUnit_mul _ _ hc⟩

private theorem source_bridge :
    source_series = (1 + X) *
      expand 2 (by decide) D5.S3.Constants.Moments.A331474HankelBridge.F0 := by
  let C : PowerSeries ℤ := D5.S3.Constants.Moments.A331474HankelBridge.catalanInt
  let D : PowerSeries ℤ := D5.S3.Constants.Moments.A331474HankelBridge.F0
  have hcat : C ^ 2 * X + 1 = C := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simpa [C, D5.S3.Constants.Moments.A331474HankelBridge.catalanInt] using h
  have hd := congrArg (derivative (R := ℤ)) hcat
  simp only [map_add, Derivation.leibniz, derivative_pow,
    derivative_X, derivative_one, smul_eq_mul] at hd
  have hder : D * (1 - 2 * X * C) = C ^ 2 := by
    change C ^ 2 * 1 + X * (2 * C ^ (2 - 1) * D) + 0 = D at hd
    norm_num at hd
    linear_combination -hd
  have hid : D * ((1 - X * C) * (1 - 2 * X * C)) = C := by
    calc
      _ = C ^ 2 * (1 - X * C) := by rw [← hder]; ring
      _ = C := by linear_combination -C * hcat
  have he := congrArg (expand 2 (by decide) : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ) hid
  have he' : expand 2 (by decide) D * denominator = catalan_square := by
    simpa [denominator, source_root, catalan_square, C, expand_X, map_ofNat] using he
  calc
    source_series = (1 + X) * (expand 2 (by decide) D * denominator) *
        invOfUnit denominator 1 := by rw [source_series, he']
    _ = (1 + X) * expand 2 (by decide) D := by
      rw [mul_assoc, mul_assoc, denominator_inverse.2.1, mul_one]

private theorem paired_coefficients (m : ℕ) :
    a (2 * m) = Provider m ∧ a (2 * m + 1) = Provider m := by
  let T := expand 2 (by decide) D5.S3.Constants.Moments.A331474HankelBridge.F0
  have he (k : ℕ) : coeff (2 * k) T = Provider k := by
    rw [PowerSeries.coeff_expand_mul]
    exact D5.S3.Constants.Moments.A331474HankelBridge.source_moments.1 k
  have ho (k : ℕ) : coeff (2 * k + 1) T = 0 := by
    apply PowerSeries.coeff_expand_of_not_dvd
    omega
  have ha (n : ℕ) : a n = coeff n T + coeff n (X * T) := by
    rw [a, source_bridge, add_mul, one_mul, map_add]
  constructor
  · cases m with
    | zero =>
      rw [ha]
      simpa using he 0
    | succ m =>
      rw [ha, he]
      have hx : coeff (2 * (m + 1)) (X * T) = coeff (2 * m + 1) T := by
        simpa only [pow_one, show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
          using coeff_X_pow_mul T 1 (2 * m + 1)
      rw [hx, ho, add_zero]
  · rw [ha, ho]
    have hx : coeff (2 * m + 1) (X * T) = coeff (2 * m) T := by
      simpa only [pow_one] using coeff_X_pow_mul T 1 (2 * m)
    rw [hx, he, zero_add]

private theorem adjacent (m : ℕ) :
    ((m : ℤ) + 1) * (m + 3) * Provider (m + 1) =
      2 * (m + 2) * (2 * m + 3) * Provider m := by
  have h1 := congrArg (Nat.cast (R := ℤ)) (Nat.choose_mul_succ_eq (2 * m + 2) m)
  have h2 := congrArg (Nat.cast (R := ℤ)) (Nat.choose_mul_succ_eq (2 * m + 3) m)
  have h3 := congrArg (Nat.cast (R := ℤ)) (Nat.choose_succ_right_eq (2 * m + 4) m)
  rw [show 2 * m + 2 + 1 - m = m + 3 by omega] at h1
  rw [show 2 * m + 3 + 1 - m = m + 4 by omega] at h2
  rw [show 2 * m + 4 - m = m + 4 by omega] at h3
  push_cast at h1 h2 h3
  dsimp [Provider, D5.S3.Constants.Moments.A331474HankelBridge.b]
  have hi : 2 * (m + 1) + 2 = 2 * m + 4 := by omega
  rw [hi]
  linear_combination (m + 3 : ℤ) * h3 - (m + 3 : ℤ) * h2 -
    2 * (m + 2 : ℤ) * h1

/-- Mathar's exact printed recurrence for every legal source index, together
with the normalized square-root, genuine unit inverse and full series bridge. -/
theorem result :
    (constantCoeff source_root = 1 ∧ source_root ^ 2 = 1 - 4 * X ^ 2 ∧
      ∀ r : PowerSeries ℤ, constantCoeff r = 1 → r ^ 2 = 1 - 4 * X ^ 2 →
        r = source_root) ∧
    (IsUnit denominator ∧ denominator * invOfUnit denominator 1 = 1 ∧
      invOfUnit denominator 1 * denominator = 1) ∧
    source_series = (1 + X) *
      expand 2 (by decide) D5.S3.Constants.Moments.A331474HankelBridge.F0 ∧
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℤ) + 4) * (31 * n - 12) * a n +
      (37 * (n : ℤ) ^ 2 + 24 * n - 156) * a (n - 1) -
      4 * (31 * (n : ℤ) ^ 2 + 81 * n + 24) * a (n - 2) -
      4 * (37 * (n : ℤ) + 24) * (n - 1) * a (n - 3) = 0 := by
  refine ⟨root_spec, denominator_inverse, source_bridge, ?_⟩
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul m] at hn ⊢
    have hm : 2 ≤ m := by omega
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [show 2 * (k + 2) - 1 = 2 * (k + 1) + 1 by omega,
      show 2 * (k + 2) - 2 = 2 * (k + 1) by omega,
      show 2 * (k + 2) - 3 = 2 * k + 1 by omega,
      (paired_coefficients (k + 2)).1, (paired_coefficients (k + 1)).2,
      (paired_coefficients (k + 1)).1, (paired_coefficients k).2]
    push_cast
    have h1 := adjacent (k + 1)
    have h0 := adjacent k
    push_cast at h1
    have hk : (k : ℤ) + 2 ≠ 0 := by positivity
    apply (mul_left_cancel₀ hk)
    linear_combination 4 * (31 * (k + 2 : ℤ) - 6) * h1 +
      4 * (37 * (k + 2 : ℤ) + 12) * h0
  · have hm : 1 ≤ m := by omega
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (k + 1) + 1 - 1 = 2 * (k + 1) by omega,
      show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega,
      show 2 * (k + 1) + 1 - 3 = 2 * k by omega,
      (paired_coefficients (k + 1)).2, (paired_coefficients (k + 1)).1,
      (paired_coefficients k).2, (paired_coefficients k).1]
    push_cast
    have h := adjacent k
    linear_combination 272 * h

end D5.S3.Constants.Moments.A117187MatharRecurrence
