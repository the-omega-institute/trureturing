/- GID: D5/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA194767SecondKindDiagonal
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Rat.Lemmas]
   utility: none
   digest: The A194767 fourth diagonal has denominators (m+1)(m+2)/gcd(3,m+2). -/

import D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The fourth diagonal of the second-kind companion of Curtz's array. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA194767SecondKindDiagonal

open D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture PowerSeries

/-- The fourth diagonal `C(m, m + 3) = 2 B(m, m + 4) - B(m, m + 3)` of the second-kind array. -/
def C3 (m : ℕ) : ℚ := 2 * triangle m 4 - triangle m 3

/-- Its reduced denominator `d_m`. -/
def d (m : ℕ) : ℕ := (C3 m).den

/-- A051176: `n / 3` if `3 ∣ n`, else `n`, offset 0. -/
def A051176 (n : ℕ) : ℕ := if n % 3 = 0 then n / 3 else n

/-- A146535: the numerator of `(2n - 1) / 3`, offset 1. -/
def A146535 (n : ℕ) : ℤ := ((2 * (n : ℚ) - 1) / 3).num

private theorem t1 (m : ℕ) : triangle m 1 = (-1) ^ m / (m + 1) := by rw [triangle]

private theorem tstep (m k : ℕ) : triangle m (k + 2) = triangle m (k + 1) + triangle (m + 1) k := by
  rw [triangle]

private theorem t2 (m : ℕ) : triangle m 2 = triangle m 1 := by
  have h := tstep m 0
  have h0 : triangle (m + 1) 0 = 0 := by rw [triangle]
  rw [h0, add_zero] at h
  exact h

private theorem t3 (m : ℕ) : triangle m 3 = triangle m 2 + triangle (m + 1) 1 := tstep m 1

private theorem t4 (m : ℕ) : triangle m 4 = triangle m 3 + triangle (m + 1) 2 := tstep m 2

private theorem C3_eq (m : ℕ) : C3 m = (-1) ^ (m + 1) * (2 * m + 1) / ((m + 1) * (m + 2)) := by
  unfold C3
  simp only [t4, t3, t2, t1]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- If `a` and `b` are coprime with `b > 0`, the reduced denominator of `± a / b` is `b`. -/
private theorem den_of_coprime (s : ℚ) (hs : s = 1 ∨ s = -1) (a b : ℤ) (hb : 0 < b)
    (h : IsCoprime a b) :
    ((s * a / b : ℚ).den : ℤ) = b := by
  have hc : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
  rcases hs with rfl | rfl
  · simpa using Rat.den_div_eq_of_coprime hb hc
  · rw [show (-1 * (a : ℚ) / b) = -((a : ℚ) / b) by ring, Rat.den_neg_eq_den]
    exact Rat.den_div_eq_of_coprime hb hc

private theorem sign (m : ℕ) : (-1 : ℚ) ^ (m + 1) = 1 ∨ (-1 : ℚ) ^ (m + 1) = -1 := by
  rcases neg_one_pow_eq_or ℚ (m + 1) with h | h <;> simp [h]

private theorem d_val (k : ℕ) :
    d (3 * k) = (3 * k + 1) * (3 * k + 2) ∧ d (3 * k + 1) = (k + 1) * (3 * k + 2) ∧
      d (3 * k + 2) = 3 * (k + 1) * (3 * k + 4) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := den_of_coprime _ (sign (3 * k)) (6 * k + 1) ((3 * k + 1) * (3 * k + 2))
      (by positivity) ⟨1 + 2 * k * (6 * k + 5), -8 * k, by ring⟩
    have e : C3 (3 * k) = (-1) ^ (3 * k + 1) * ((6 * k + 1 : ℤ) : ℚ) /
        (((3 * k + 1) * (3 * k + 2) : ℤ) : ℚ) := by
      rw [C3_eq]; push_cast; ring
    unfold d; rw [e]; exact_mod_cast h
  · have h := den_of_coprime _ (sign (3 * k + 1)) (2 * k + 1) ((k + 1) * (3 * k + 2))
      (by positivity) ⟨-(6 * k + 7), 4, by ring⟩
    have e : C3 (3 * k + 1) = (-1) ^ (3 * k + 1 + 1) * ((2 * k + 1 : ℤ) : ℚ) /
        (((k + 1) * (3 * k + 2) : ℤ) : ℚ) := by
      rw [C3_eq]; push_cast; field_simp; ring
    unfold d; rw [e]; exact_mod_cast h
  · have h := den_of_coprime _ (sign (3 * k + 2)) (6 * k + 5) (3 * (k + 1) * (3 * k + 4))
      (by positivity) ⟨-((2 * k + 2) * (6 * k + 9) + 1), 8 * k + 8, by ring⟩
    have e : C3 (3 * k + 2) = (-1) ^ (3 * k + 2 + 1) * ((6 * k + 5 : ℤ) : ℚ) /
        ((3 * (k + 1) * (3 * k + 4) : ℤ) : ℚ) := by
      rw [C3_eq]; push_cast; ring
    unfold d; rw [e]; exact_mod_cast h

private theorem split3 (n : ℕ) : ∃ k r, r < 3 ∧ n = 3 * k + r :=
  ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩

private theorem d_formula (m : ℕ) : d m = (m + 1) * (m + 2) / Nat.gcd 3 (m + 2) := by
  obtain ⟨k, r, hr, rfl⟩ := split3 m
  obtain ⟨h0, h1, h2⟩ := d_val k
  interval_cases r
  · rw [Nat.add_zero, h0, Nat.gcd_rec, show (3 * k + 2) % 3 = 2 by omega]
    norm_num
  · rw [h1, show 3 * k + 1 + 2 = 3 * (k + 1) by ring, Nat.gcd_mul_right_right]
    rw [show (3 * k + 1 + 1) * (3 * (k + 1)) = 3 * ((k + 1) * (3 * k + 2)) by ring]
    simp
  · rw [h2, Nat.gcd_rec, show (3 * k + 2 + 2) % 3 = 1 by omega]
    norm_num
    ring

private theorem d_eq (m : ℕ) : (d m : ℤ) =
    if m % 3 = 0 then (3 * (m / 3) + 1) * (3 * (m / 3) + 2)
    else if m % 3 = 1 then (m / 3 + 1) * (3 * (m / 3) + 2)
    else 3 * (m / 3 + 1) * (3 * (m / 3) + 4) := by
  obtain ⟨k, r, hr, rfl⟩ := split3 m
  obtain ⟨h0, h1, h2⟩ := d_val k
  rw [show (3 * k + r) / 3 = k by omega, show (3 * k + r) % 3 = r by omega]
  interval_cases r <;> simp_all

private theorem d_rec (m : ℕ) : (d (m + 9) : ℤ) = 3 * d (m + 6) - 3 * d (m + 3) + d m := by
  rw [d_eq, d_eq (m + 6), d_eq (m + 3), d_eq m,
    show (m + 9) % 3 = m % 3 by omega, show (m + 6) % 3 = m % 3 by omega,
    show (m + 3) % 3 = m % 3 by omega, show (m + 9) / 3 = m / 3 + 3 by omega,
    show (m + 6) / 3 = m / 3 + 2 by omega, show (m + 3) / 3 = m / 3 + 1 by omega]
  split_ifs <;> push_cast <;> ring

private theorem d_small : (d 0 : ℤ) = 2 ∧ (d 1 : ℤ) = 2 ∧ (d 2 : ℤ) = 12 ∧ (d 3 : ℤ) = 20 ∧
    (d 4 : ℤ) = 10 ∧ (d 5 : ℤ) = 42 ∧ (d 6 : ℤ) = 56 ∧ (d 7 : ℤ) = 24 ∧ (d 8 : ℤ) = 90 := by
  simp only [d_eq]; norm_num

private theorem d_gf_key : mk (fun m => (d m : ℤ)) *
      (1 - X ^ 3 - X ^ 3 - X ^ 3 + X ^ 6 + X ^ 6 + X ^ 6 - X ^ 9) =
    C 2 + C 2 * X + C 12 * X ^ 2 + C 14 * X ^ 3 + C 4 * X ^ 4 + C 6 * X ^ 5 + C 2 * X ^ 6 := by
  have hc : ∀ n, coeff n (2 : ℤ⟦X⟧) = if n = 0 then 2 else 0 := by
    intro n; rw [show (2 : ℤ⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C]
  have hcc : constantCoeff (2 : ℤ⟦X⟧) = 2 := map_ofNat _ 2
  simp only [mul_add, mul_sub, mul_one]
  ext n
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := d_small
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, hc, hcc,
      a0, a1, a2, a3, a4, a5, a6, a7, a8]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have h := d_rec m
    simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, hc,
      show m + 9 - 3 = m + 6 by omega, show m + 9 - 6 = m + 3 by omega]
    linarith

private theorem d_gf : mk (fun m => (d m : ℤ)) * (1 - X ^ 3) ^ 3 =
    2 * (1 + X + 6 * X ^ 2 + 7 * X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5 + X ^ 6) := by
  have h := d_gf_key
  simp only [map_ofNat] at h
  linear_combination h

private theorem A051176_ident (m : ℕ) : d m = (m + 1) * A051176 (m + 2) := by
  have h := d_eq m
  unfold A051176
  obtain ⟨k, r, hr, rfl⟩ := split3 m
  rw [show (3 * k + r) / 3 = k by omega, show (3 * k + r) % 3 = r by omega] at h
  interval_cases r
  · rw [show (3 * k + 0 + 2) % 3 = 2 by omega]; simp at h ⊢; exact_mod_cast h
  · rw [show (3 * k + 1 + 2) % 3 = 0 by omega, show (3 * k + 1 + 2) / 3 = k + 1 by omega]
    simp at h ⊢; linarith
  · rw [show (3 * k + 2 + 2) % 3 = 1 by omega]; simp at h ⊢; linarith

private theorem num_of_coprime (a b : ℤ) (hb : 0 < b) (h : IsCoprime a b) : ((a : ℚ) / b).num = a :=
  Rat.num_div_eq_of_coprime hb (Int.isCoprime_iff_gcd_eq_one.mp h)

private theorem A146535_val (k : ℕ) :
    A146535 (3 * k + 1) = 6 * k + 1 ∧ A146535 (3 * k + 2) = 2 * k + 1 ∧
      A146535 (3 * k + 3) = 6 * k + 5 := by
  unfold A146535
  refine ⟨?_, ?_, ?_⟩
  · have := num_of_coprime (6 * k + 1) 3 (by norm_num) ⟨1, -(2 * k), by ring⟩
    push_cast at this ⊢; rw [show 2 * (3 * (k : ℚ) + 1) - 1 = 6 * k + 1 by ring]; exact this
  · rw [show (2 * ((3 * k + 2 : ℕ) : ℚ) - 1) / 3 = ((2 * k + 1 : ℤ) : ℚ) by push_cast; ring]
    exact Rat.num_intCast _
  · have := num_of_coprime (6 * k + 5) 3 (by norm_num) ⟨-1, 2 * k + 2, by ring⟩
    push_cast at this ⊢; rw [show 2 * (3 * (k : ℚ) + 3) - 1 = 6 * k + 5 by ring]; exact this

private theorem numerator_shift (m : ℕ) : C3 m = (-1) ^ (m + 1) * A146535 (m + 1) / d m := by
  obtain ⟨k, r, hr, rfl⟩ := split3 m
  obtain ⟨h0, h1, h2⟩ := d_val k
  obtain ⟨n0, n1, n2⟩ := A146535_val k
  rw [C3_eq]
  interval_cases r
  · simp only [Nat.add_zero] at *
    rw [h0, n0]; push_cast; ring
  · rw [h1, show 3 * k + 1 + 1 = 3 * k + 2 by ring, n1]; push_cast; field_simp; ring
  · rw [h2, show 3 * k + 2 + 1 = 3 * k + 3 by ring, n2]; push_cast; field_simp; ring

private theorem unshifted_fails : C3 2 ≠ (-1) ^ (2 + 1) * A146535 2 / d 2 := by
  have hd : (d 2 : ℚ) = 12 := by exact_mod_cast d_small.2.2.1
  have ha : A146535 2 = 1 := by unfold A146535; norm_num
  rw [C3_eq, hd, ha]
  norm_num

/-- `A306368(n)`: the reduced numerator of `(n + 3)(n + 4) / ((n + 1)(n + 2))`. -/
def A306368 (n : ℕ) : ℤ := ((((n + 3) * (n + 4) : ℕ) : ℚ) / ((n + 1) * (n + 2) : ℕ)).num

private theorem A306368_of (m : ℕ) (N0 N1 D0 D1 : ℤ) (hD : 0 < D0 * D1)
    (h00 : IsCoprime N0 D0) (h01 : IsCoprime N0 D1) (h10 : IsCoprime N1 D0)
    (h11 : IsCoprime N1 D1)
    (e : ((m : ℚ) + 3) * (m + 4) * (D0 * D1) = (N0 * N1) * ((m + 1) * (m + 2))) :
    A306368 m = N0 * N1 := by
  have hc : IsCoprime (N0 * N1) (D0 * D1) :=
    IsCoprime.mul_left (IsCoprime.mul_right h00 h01) (IsCoprime.mul_right h10 h11)
  have hD' : ((D0 * D1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold A306368
  rw [show (((m + 3) * (m + 4) : ℕ) : ℚ) / ((m + 1) * (m + 2) : ℕ) =
      ((N0 * N1 : ℤ) : ℚ) / ((D0 * D1 : ℤ) : ℚ) by
    rw [div_eq_div_iff (by positivity) hD']; push_cast; linarith]
  exact num_of_coprime _ _ hD hc

private theorem split6 (n : ℕ) : ∃ k r, r < 6 ∧ n = 6 * k + r :=
  ⟨n / 6, n % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 6).symm⟩

private theorem A306368_ident (m : ℕ) : (d (m + 2) : ℤ) = 2 * A306368 m := by
  obtain ⟨k, r, hr, rfl⟩ := split6 m
  rw [d_eq]
  interval_cases r
  · rw [A306368_of _ (6 * k + 3) (3 * k + 2) (6 * k + 1) (3 * k + 1) (by positivity)
      ⟨-27 * k - 4, 27 * k + 13, by ring⟩ ⟨-30 * k - 9, 60 * k + 28, by ring⟩
      ⟨-28 * k - 4, 14 * k + 9, by ring⟩ ⟨-30 * k - 9, 30 * k + 19, by ring⟩
      (by push_cast; ring),
      show (6 * k + 0 + 2) % 3 = 2 by omega, show (6 * k + 0 + 2) / 3 = 2 * k by omega]
    simp; ring
  · rw [A306368_of _ (3 * k + 2) (6 * k + 5) (3 * k + 1) (6 * k + 3) (by positivity)
      ⟨-30 * k - 9, 30 * k + 19, by ring⟩ ⟨-30 * k - 13, 15 * k + 9, by ring⟩
      ⟨-28 * k - 9, 56 * k + 46, by ring⟩ ⟨-27 * k - 13, 27 * k + 22, by ring⟩
      (by push_cast; ring),
      show (6 * k + 1 + 2) % 3 = 0 by omega, show (6 * k + 1 + 2) / 3 = 2 * k + 1 by omega]
    simp; ring
  · rw [A306368_of _ (6 * k + 5) (k + 1) (2 * k + 1) (3 * k + 2) (by positivity)
      ⟨-29 * k - 14, 87 * k + 71, by ring⟩ ⟨-30 * k - 19, 60 * k + 48, by ring⟩
      ⟨-30 * k - 13, 15 * k + 14, by ring⟩ ⟨-30 * k - 17, 10 * k + 9, by ring⟩
      (by push_cast; ring),
      show (6 * k + 2 + 2) % 3 = 1 by omega, show (6 * k + 2 + 2) / 3 = 2 * k + 1 by omega]
    simp; ring
  · rw [A306368_of _ (3 * k + 3) (6 * k + 7) (3 * k + 2) (6 * k + 5) (by positivity)
      ⟨-30 * k - 19, 30 * k + 29, by ring⟩ ⟨-30 * k - 23, 15 * k + 14, by ring⟩
      ⟨-29 * k - 19, 58 * k + 67, by ring⟩ ⟨-27 * k - 22, 27 * k + 31, by ring⟩
      (by push_cast; ring),
      show (6 * k + 3 + 2) % 3 = 2 by omega, show (6 * k + 3 + 2) / 3 = 2 * k + 1 by omega]
    simp; ring
  · rw [A306368_of _ (6 * k + 7) (3 * k + 4) (6 * k + 5) (3 * k + 3) (by positivity)
      ⟨-27 * k - 22, 27 * k + 31, by ring⟩ ⟨-30 * k - 29, 60 * k + 68, by ring⟩
      ⟨-26 * k - 21, 13 * k + 17, by ring⟩ ⟨-30 * k - 29, 30 * k + 39, by ring⟩
      (by push_cast; ring),
      show (6 * k + 4 + 2) % 3 = 0 by omega, show (6 * k + 4 + 2) / 3 = 2 * k + 2 by omega]
    simp; ring
  · rw [A306368_of _ (3 * k + 4) (2 * k + 3) (k + 1) (6 * k + 7) (by positivity)
      ⟨-30 * k - 29, 90 * k + 117, by ring⟩ ⟨-24 * k - 26, 12 * k + 15, by ring⟩
      ⟨-30 * k - 29, 60 * k + 88, by ring⟩ ⟨-27 * k - 30, 9 * k + 13, by ring⟩
      (by push_cast; ring),
      show (6 * k + 5 + 2) % 3 = 1 by omega, show (6 * k + 5 + 2) / 3 = 2 * k + 2 by omega]
    simp; ring

/-- The fourth diagonal of the A194767 second-kind array: its exact value, reduced
denominators with their residue formulas and generating function, the A051176 and A306368
formulas, and the corrected A146535 numerator formula, which fails at `m = 2` with the
unshifted index. -/
theorem result :
    (∀ m, C3 m = (-1) ^ (m + 1) * (2 * m + 1) / ((m + 1) * (m + 2))) ∧
    (∀ m, d m = (m + 1) * (m + 2) / Nat.gcd 3 (m + 2)) ∧
    (∀ k, d (3 * k) = (3 * k + 1) * (3 * k + 2) ∧ d (3 * k + 1) = (k + 1) * (3 * k + 2) ∧
      d (3 * k + 2) = 3 * (k + 1) * (3 * k + 4)) ∧
    mk (fun m => (d m : ℤ)) * (1 - X ^ 3) ^ 3 =
      2 * (1 + X + 6 * X ^ 2 + 7 * X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5 + X ^ 6) ∧
    (∀ m, d m = (m + 1) * A051176 (m + 2)) ∧ (∀ m, (d (m + 2) : ℤ) = 2 * A306368 m) ∧
    (∀ m, C3 m = (-1) ^ (m + 1) * A146535 (m + 1) / d m) ∧
    C3 2 ≠ (-1) ^ (2 + 1) * A146535 2 / d 2 :=
  ⟨C3_eq, d_formula, d_val, d_gf, A051176_ident, A306368_ident, numerator_shift,
    unshifted_fails⟩

end D5.S1.Recurrence.Residue.OEISA194767SecondKindDiagonal
