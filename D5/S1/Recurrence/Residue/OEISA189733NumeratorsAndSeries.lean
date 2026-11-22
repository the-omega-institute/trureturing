/- GID: D5/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA189733NumeratorsAndSeries
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.NoZeroDivisors]
   utility: none
   digest: Curtz's numerators repeat (0,1,1,1,0,-1) and both sequences have rational series. -/

import D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Numerators, denominator recurrence and generating functions of the zeroth row. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA189733NumeratorsAndSeries

open D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture PowerSeries

/-- Reduced numerators of the zeroth row. -/
def p (n : ℕ) : ℤ := (triangle 0 n).num

private theorem p_six (k : ℕ) :
    p (6 * k) = 0 ∧ p (6 * k + 1) = 1 ∧ p (6 * k + 2) = 1 ∧ p (6 * k + 3) = 1 ∧
      p (6 * k + 4) = 0 ∧ p (6 * k + 5) = -1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := triangle_six k
  have hn (d : ℕ) (h : 0 < d) : (1 / (d : ℚ)).num = 1 := by
    rw [one_div]; exact Rat.inv_natCast_num_of_pos h
  refine ⟨by simp [p, h0], ?_, ?_, ?_, by simp [p, h4], ?_⟩
  · have := hn (3 * k + 1) (by omega); push_cast at this; rw [p, h1, this]
  · have := hn (2 * k + 1) (by omega); push_cast at this; rw [p, h2, this]
  · have := hn (3 * k + 2) (by omega); push_cast at this; rw [p, h3, this]
  · have := hn (6 * k + 6) (by omega); push_cast at this
    rw [p, h5, Rat.num_neg_eq_neg_num, this]

private theorem split6 (n : ℕ) : ∃ k r, r < 6 ∧ n = 6 * k + r :=
  ⟨n / 6, n % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 6).symm⟩

/-- The numerators have period six. -/
private theorem p_period (n : ℕ) : p (n + 6) = p n := by
  obtain ⟨k, r, hr, rfl⟩ := split6 n
  have e : 6 * k + r + 6 = 6 * (k + 1) + r := by ring
  rw [e]
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := p_six k
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := p_six (k + 1)
  interval_cases r <;> simp_all

private theorem a_val (k : ℕ) :
    (a (6 * k) : ℤ) = 1 ∧ (a (6 * k + 1) : ℤ) = 3 * k + 1 ∧ (a (6 * k + 2) : ℤ) = 2 * k + 1 ∧
      (a (6 * k + 3) : ℤ) = 3 * k + 2 ∧ (a (6 * k + 4) : ℤ) = 1 ∧
      (a (6 * k + 5) : ℤ) = 6 * k + 6 := by
  have h := result k
  simp only [Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [h0, h1, h2, h3, h4, h5]

/-- The denominators satisfy `a_{n+12} = 2 a_{n+6} - a_n`. -/
private theorem a_rec (n : ℕ) : (a (n + 12) : ℤ) = 2 * a (n + 6) - a n := by
  obtain ⟨k, r, hr, rfl⟩ := split6 n
  have e1 : 6 * k + r + 6 = 6 * (k + 1) + r := by ring
  have e2 : 6 * k + r + 12 = 6 * (k + 2) + r := by ring
  rw [e1, e2]
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := a_val k
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := a_val (k + 1)
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := a_val (k + 2)
  interval_cases r <;> simp only [Nat.add_zero, a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5,
    c0, c1, c2, c3, c4, c5] <;> push_cast <;> ring

/-- Numerator values on residues. -/
private def pv : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | _ => -1

private theorem p_eq (n : ℕ) : p n = pv (n % 6) := by
  obtain ⟨k, r, hr, rfl⟩ := split6 n
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := p_six k
  have : (6 * k + r) % 6 = r := by omega
  rw [this]
  interval_cases r <;> simp_all [pv]

private theorem a_small :
    (a 0 : ℤ) = 1 ∧ (a 1 : ℤ) = 1 ∧ (a 2 : ℤ) = 1 ∧ (a 3 : ℤ) = 2 ∧ (a 4 : ℤ) = 1 ∧
    (a 5 : ℤ) = 6 ∧ (a 6 : ℤ) = 1 ∧ (a 7 : ℤ) = 4 ∧ (a 8 : ℤ) = 3 ∧ (a 9 : ℤ) = 5 ∧
    (a 10 : ℤ) = 1 ∧ (a 11 : ℤ) = 12 := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := a_val 0
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := a_val 1
  norm_num at a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
  exact ⟨by exact_mod_cast a0, by exact_mod_cast a1, by exact_mod_cast a2, by exact_mod_cast a3,
    by exact_mod_cast a4, by exact_mod_cast a5, by exact_mod_cast b0, by exact_mod_cast b1,
    by exact_mod_cast b2, by exact_mod_cast b3, by exact_mod_cast b4, by exact_mod_cast b5⟩

/-- Barker's generating function of the denominators. -/
private theorem a_gf :
    mk (fun n => (a n : ℤ)) * (1 - X ^ 6) ^ 2 =
      1 + X + X ^ 2 + 2 * X ^ 3 + X ^ 4 + 6 * X ^ 5 - X ^ 6 + 2 * X ^ 7 + X ^ 8 + X ^ 9 -
        X ^ 10 := by
  have hexp : (1 - X ^ 6 : ℤ⟦X⟧) ^ 2 = 1 - X ^ 6 - X ^ 6 + X ^ 12 := by ring
  rw [hexp]
  simp only [mul_add, mul_sub, mul_one]
  ext n
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := a_small
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, coeff_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    have h := a_rec m
    simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, coeff_one,
      show m + 12 - 6 = m + 6 by omega]
    linarith

private theorem p_small : p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 1 ∧ p 3 = 1 ∧ p 4 = 0 ∧ p 5 = -1 := by
  simpa using p_six 0

/-- The numerators' generating function. -/
private theorem p_gf : mk (fun n => p n) * (1 - X ^ 6) = X + X ^ 2 + X ^ 3 - X ^ 5 := by
  simp only [mul_sub, mul_one]
  ext n
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := p_small
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, p0, p1, p2, p3, p4, p5]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, p_period, show m + 6 ≠ 1 by omega,
      show m + 6 ≠ 2 by omega, show m + 6 ≠ 3 by omega, show m + 6 ≠ 5 by omega]

/-- The reduced form of the numerators' generating function. -/
private theorem p_gf_reduced :
    mk (fun n => p n) * ((1 - X) * (1 - X + X ^ 2) * (1 + X + X ^ 2)) =
      X * (1 + X ^ 2 - X ^ 3) := by
  have h1 : (1 + X : ℤ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (constantCoeff) h
    simp at this
  apply mul_left_cancel₀ h1
  have := p_gf
  linear_combination this

/-- Hurt's closed form for the numerators. -/
private theorem p_closed (n : ℕ) :
    (p n : ℚ) = (1 + (-1 : ℚ) ^ (((n : ℤ) - 1) / 3)) / 2 - (((n : ℤ) + 1) / 6 : ℤ) +
      ((n : ℤ) / 6 : ℤ) := by
  obtain ⟨k, r, hr, rfl⟩ := split6 n
  rw [p_eq, show (6 * k + r) % 6 = r by omega]
  have hz (j : ℤ) : (-1 : ℚ) ^ (2 * (k : ℤ) + j) = (-1) ^ j := by
    rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num
  interval_cases r
  · rw [show (((6 * k + 0 : ℕ) : ℤ) - 1) / 3 = 2 * (k : ℤ) + (-1) by omega, hz,
      show (((6 * k + 0 : ℕ) : ℤ) + 1) / 6 = (k : ℤ) + 0 by omega,
      show ((6 * k + 0 : ℕ) : ℤ) / 6 = (k : ℤ) by omega]
    norm_num [pv]
  · rw [show (((6 * k + 1 : ℕ) : ℤ) - 1) / 3 = 2 * (k : ℤ) + (0) by omega, hz,
      show (((6 * k + 1 : ℕ) : ℤ) + 1) / 6 = (k : ℤ) + 0 by omega,
      show ((6 * k + 1 : ℕ) : ℤ) / 6 = (k : ℤ) by omega]
    norm_num [pv]
  · rw [show (((6 * k + 2 : ℕ) : ℤ) - 1) / 3 = 2 * (k : ℤ) + (0) by omega, hz,
      show (((6 * k + 2 : ℕ) : ℤ) + 1) / 6 = (k : ℤ) + 0 by omega,
      show ((6 * k + 2 : ℕ) : ℤ) / 6 = (k : ℤ) by omega]
    norm_num [pv]
  · rw [show (((6 * k + 3 : ℕ) : ℤ) - 1) / 3 = 2 * (k : ℤ) + (0) by omega, hz,
      show (((6 * k + 3 : ℕ) : ℤ) + 1) / 6 = (k : ℤ) + 0 by omega,
      show ((6 * k + 3 : ℕ) : ℤ) / 6 = (k : ℤ) by omega]
    norm_num [pv]
  · rw [show (((6 * k + 4 : ℕ) : ℤ) - 1) / 3 = 2 * (k : ℤ) + (1) by omega, hz,
      show (((6 * k + 4 : ℕ) : ℤ) + 1) / 6 = (k : ℤ) + 0 by omega,
      show ((6 * k + 4 : ℕ) : ℤ) / 6 = (k : ℤ) by omega]
    norm_num [pv]
  · rw [show (((6 * k + 5 : ℕ) : ℤ) - 1) / 3 = 2 * (k : ℤ) + (1) by omega, hz,
      show (((6 * k + 5 : ℕ) : ℤ) + 1) / 6 = (k : ℤ) + 1 by omega,
      show ((6 * k + 5 : ℕ) : ℤ) / 6 = (k : ℤ) by omega]
    norm_num [pv]

/-- The five-term recurrence of the numerators. -/
private theorem p_rec5 (n : ℕ) :
    p (n + 5) = p (n + 4) - p (n + 3) + p (n + 2) - p (n + 1) + p n := by
  simp only [p_eq]
  have : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [show (n + 5) % 6 = (n % 6 + 5) % 6 by omega, show (n + 4) % 6 = (n % 6 + 4) % 6 by omega,
    show (n + 3) % 6 = (n % 6 + 3) % 6 by omega, show (n + 2) % 6 = (n % 6 + 2) % 6 by omega,
    show (n + 1) % 6 = (n % 6 + 1) % 6 by omega]
  interval_cases n % 6 <;> rfl

/-- Six is the least period of the numerators. -/
private theorem p_least_period (d : ℕ) (hd : 0 < d) (hd6 : d < 6) : ∃ n, p (n + d) ≠ p n := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := p_small
  interval_cases d
  · exact ⟨0, by simp [p0, p1]⟩
  · exact ⟨0, by simp [p0, p2]⟩
  · exact ⟨0, by simp [p0, p3]⟩
  · exact ⟨1, by norm_num [p1, p5]⟩
  · exact ⟨0, by simp [p0, p5]⟩

private theorem p_multiple_period (q n : ℕ) : p (n + 6 * q) = p n := by
  induction q with
  | zero => simp
  | succ q ih => rw [show n + 6 * (q + 1) = n + 6 * q + 6 by ring, p_period, ih]

private theorem period_dvd (d : ℕ) (hd : ∀ n, p (n + d) = p n) : 6 ∣ d := by
  obtain ⟨q, r, hr, rfl⟩ := split6 d
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · exact ⟨q, by omega⟩
  · obtain ⟨n, hn⟩ := p_least_period r hpos hr
    exact absurd (by rw [← hd n, show n + (6 * q + r) = n + r + 6 * q by ring,
      p_multiple_period]) hn

/-- The theorem combining the numerator period, the denominator recurrence, Barker's generating
function, both numerator generating functions, Hurt's closed form and the five-term recurrence. -/
theorem result :
    (∀ k, p (6 * k) = 0 ∧ p (6 * k + 1) = 1 ∧ p (6 * k + 2) = 1 ∧ p (6 * k + 3) = 1 ∧
      p (6 * k + 4) = 0 ∧ p (6 * k + 5) = -1) ∧
    (∀ n, p (n + 6) = p n) ∧
    (∀ d, (∀ n, p (n + d) = p n) → 6 ∣ d) ∧
    (∀ n, 12 ≤ n → (a n : ℤ) = 2 * a (n - 6) - a (n - 12)) ∧
    mk (fun n => (a n : ℤ)) * (1 - X ^ 6) ^ 2 =
      1 + X + X ^ 2 + 2 * X ^ 3 + X ^ 4 + 6 * X ^ 5 - X ^ 6 + 2 * X ^ 7 + X ^ 8 + X ^ 9 -
        X ^ 10 ∧
    mk (fun n => p n) * (1 - X ^ 6) = X + X ^ 2 + X ^ 3 - X ^ 5 ∧
    mk (fun n => p n) * ((1 - X) * (1 - X + X ^ 2) * (1 + X + X ^ 2)) =
      X * (1 + X ^ 2 - X ^ 3) ∧
    (∀ n : ℕ, (p n : ℚ) = (1 + (-1 : ℚ) ^ ⌊((n : ℚ) - 1) / 3⌋) / 2 - ⌊((n : ℚ) + 1) / 6⌋ +
      ⌊(n : ℚ) / 6⌋) ∧
    (∀ n, 5 ≤ n → p n = p (n - 1) - p (n - 2) + p (n - 3) - p (n - 4) + p (n - 5)) := by
  refine ⟨p_six, p_period, period_dvd, ?_, a_gf, p_gf, p_gf_reduced, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    rw [show m + 12 - 6 = m + 6 by omega, show m + 12 - 12 = m by omega]
    exact a_rec m
  · intro n
    have h1 : ⌊((n : ℚ) - 1) / 3⌋ = ((n : ℤ) - 1) / 3 := by
      have h := Rat.floor_intCast_div_natCast ((n : ℤ) - 1) 3
      push_cast at h; exact h
    have h2 : ⌊((n : ℚ) + 1) / 6⌋ = ((n : ℤ) + 1) / 6 := by
      have h := Rat.floor_intCast_div_natCast ((n : ℤ) + 1) 6
      push_cast at h; exact h
    have h3 : ⌊(n : ℚ) / 6⌋ = (n : ℤ) / 6 := by
      have h := Rat.floor_intCast_div_natCast (n : ℤ) 6
      push_cast at h; exact h
    rw [h1, h2, h3]
    exact p_closed n
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show m + 5 - 5 = m by omega]
    exact p_rec5 m

end D5.S1.Recurrence.Residue.OEISA189733NumeratorsAndSeries
