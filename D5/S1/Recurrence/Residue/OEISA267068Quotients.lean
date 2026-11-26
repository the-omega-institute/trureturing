/- GID: D5/S1/Recurrence/Residue/OEISA267068Quotients
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA267068Quotients
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: The A267068 quotients (n+1)/a_n are integers with Barker's recurrence and series. -/

import D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The quotient sequence A267068 attached to Curtz's denominators. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA267068Quotients

open D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture PowerSeries

/-- The quotient sequence A267068, `c n = (n + 1) / a n`. -/
def c (n : ℕ) : ℕ := (n + 1) / a n

/-- A130196: period 3, repeat `[1, 2, 2]`, offset 0. -/
def A130196 (n : ℕ) : ℕ := if n % 3 = 0 then 1 else 2

/-- A047245: the `n`-th number congruent to 1, 2 or 3 modulo 6, offset 1. -/
def A047245 (n : ℕ) : ℕ := 6 * ((n - 1) / 3) + (n - 1) % 3 + 1

/-- A052901: period 3 with `a(3n) = 3` and `a(3n+1) = a(3n+2) = 2`, offset 0. -/
def A052901 (n : ℕ) : ℕ := if n % 3 = 0 then 3 else 2

/-- A047238: the `n`-th number congruent to 0 or 2 modulo 6, offset 1. -/
def A047238 (n : ℕ) : ℕ := 6 * ((n - 1) / 2) + 2 * ((n - 1) % 2)

private theorem split6 (n : ℕ) : ∃ k r, r < 6 ∧ n = 6 * k + r :=
  ⟨n / 6, n % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 6).symm⟩

private theorem a_val (k : ℕ) :
    a (6 * k) = 1 ∧ a (6 * k + 1) = 3 * k + 1 ∧ a (6 * k + 2) = 2 * k + 1 ∧
      a (6 * k + 3) = 3 * k + 2 ∧ a (6 * k + 4) = 1 ∧ a (6 * k + 5) = 6 * k + 6 := by
  have h := result k
  simp only [Prod.mk.injEq] at h
  exact h

private theorem divides (n : ℕ) : a n ∣ n + 1 := by
  obtain ⟨k, r, hr, rfl⟩ := split6 n
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := a_val k
  interval_cases r
  · simp only [Nat.add_zero, h0]; exact one_dvd _
  · rw [h1]; exact ⟨2, by ring⟩
  · rw [h2]; exact ⟨3, by ring⟩
  · rw [h3]; exact ⟨2, by ring⟩
  · rw [h4]; exact one_dvd _
  · rw [h5]

private theorem c_val (k : ℕ) :
    c (6 * k) = 6 * k + 1 ∧ c (6 * k + 1) = 2 ∧ c (6 * k + 2) = 3 ∧ c (6 * k + 3) = 2 ∧
      c (6 * k + 4) = 6 * k + 5 ∧ c (6 * k + 5) = 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := a_val k
  unfold c
  rw [h0, h1, h2, h3, h4, h5]
  refine ⟨by simp, ?_, ?_, ?_, by simp, ?_⟩
  · rw [show 6 * k + 1 + 1 = 2 * (3 * k + 1) by ring]; simp
  · rw [show 6 * k + 2 + 1 = 3 * (2 * k + 1) by ring]; simp
  · rw [show 6 * k + 3 + 1 = 2 * (3 * k + 2) by ring]; simp
  · rw [show 6 * k + 5 + 1 = 1 * (6 * k + 6) by ring]; simp

/-- Value of `c` on each residue class. -/
private def cv (k r : ℕ) : ℕ :=
  match r with
  | 0 => 6 * k + 1 | 1 => 2 | 2 => 3 | 3 => 2 | 4 => 6 * k + 5 | _ => 1

private theorem c_eq (n : ℕ) : c n = cv (n / 6) (n % 6) := by
  obtain ⟨k, r, hr, rfl⟩ := split6 n
  rw [show (6 * k + r) / 6 = k by omega, show (6 * k + r) % 6 = r by omega]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := c_val k
  interval_cases r <;> simp_all [cv]

private theorem c_rec (n : ℕ) : (c (n + 12) : ℤ) = 2 * c (n + 6) - c n := by
  rw [c_eq, c_eq (n + 6), c_eq n, show (n + 12) / 6 = n / 6 + 2 by omega,
    show (n + 12) % 6 = n % 6 by omega, show (n + 6) / 6 = n / 6 + 1 by omega,
    show (n + 6) % 6 = n % 6 by omega]
  have : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases n % 6 <;> simp [cv] <;> ring

private theorem c_small :
    (c 0 : ℤ) = 1 ∧ (c 1 : ℤ) = 2 ∧ (c 2 : ℤ) = 3 ∧ (c 3 : ℤ) = 2 ∧ (c 4 : ℤ) = 5 ∧
    (c 5 : ℤ) = 1 ∧ (c 6 : ℤ) = 7 ∧ (c 7 : ℤ) = 2 ∧ (c 8 : ℤ) = 3 ∧ (c 9 : ℤ) = 2 ∧
    (c 10 : ℤ) = 11 ∧ (c 11 : ℤ) = 1 := by
  simp only [c_eq]
  norm_num [cv]

private theorem c_gf :
    mk (fun n => (c n : ℤ)) * (1 - X ^ 6) ^ 2 =
      1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4 + X ^ 5 + 5 * X ^ 6 - 2 * X ^ 7 -
        3 * X ^ 8 - 2 * X ^ 9 + X ^ 10 - X ^ 11 := by
  have hexp : (1 - X ^ 6 : ℤ⟦X⟧) ^ 2 = 1 - X ^ 6 - X ^ 6 + X ^ 12 := by ring
  rw [hexp]
  simp only [mul_add, mul_sub, mul_one]
  ext n
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := c_small
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, coeff_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    have h := c_rec m
    simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, coeff_one,
      show m + 12 - 6 = m + 6 by omega]
    linarith

private theorem odd_ident (n : ℕ) : c (2 * n + 1) = A130196 (n + 1) := by
  rw [c_eq]; unfold A130196
  have h1 : (2 * n + 1) % 6 = 1 ∨ (2 * n + 1) % 6 = 3 ∨ (2 * n + 1) % 6 = 5 := by omega
  rcases h1 with h | h | h <;> rw [h] <;> simp [cv] <;> omega

private theorem rank_ident (n : ℕ) : c (A047245 (n + 1)) = A052901 (n + 2) := by
  rw [c_eq]; unfold A047245 A052901
  simp only [Nat.add_sub_cancel]
  have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [show (6 * (n / 3) + n % 3 + 1) / 6 = n / 3 by omega,
    show (6 * (n / 3) + n % 3 + 1) % 6 = n % 3 + 1 by omega]
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h <;> rw [h] <;> simp [cv] <;> omega

private theorem triple_ident (n : ℕ) :
    c (3 * n) + c (3 * n + 1) + c (3 * n + 2) = A047238 (n + 3) := by
  rw [c_eq, c_eq (3 * n + 1), c_eq (3 * n + 2)]; unfold A047238
  simp only [show n + 3 - 1 = n + 2 by omega]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show 3 * (k + k) = 6 * k by ring, show (6 * k) / 6 = k by omega,
      show (6 * k) % 6 = 0 by omega, show (6 * k + 1) / 6 = k by omega,
      show (6 * k + 1) % 6 = 1 by omega, show (6 * k + 2) / 6 = k by omega,
      show (6 * k + 2) % 6 = 2 by omega, show (k + k + 2) / 2 = k + 1 by omega,
      show (k + k + 2) % 2 = 0 by omega]
    simp [cv]; ring
  · rw [show 3 * (2 * k + 1) = 6 * k + 3 by ring, show (6 * k + 3) / 6 = k by omega,
      show (6 * k + 3) % 6 = 3 by omega, show (6 * k + 3 + 1) / 6 = k by omega,
      show (6 * k + 3 + 1) % 6 = 4 by omega, show (6 * k + 3 + 2) / 6 = k by omega,
      show (6 * k + 3 + 2) % 6 = 5 by omega, show (2 * k + 1 + 2) / 2 = k + 1 by omega,
      show (2 * k + 1 + 2) % 2 = 1 by omega]
    simp [cv]; ring

/-- The quotients `c n = (n + 1) / a n` of A267068 are integers with six affine residue
formulas, satisfy Barker's recurrence and generating function, and match the three sequence
identifications in the A267068 FORMULA field. -/
theorem result :
    (∀ n, a n ∣ n + 1) ∧
    (∀ k, c (6 * k) = 6 * k + 1 ∧ c (6 * k + 1) = 2 ∧ c (6 * k + 2) = 3 ∧ c (6 * k + 3) = 2 ∧
      c (6 * k + 4) = 6 * k + 5 ∧ c (6 * k + 5) = 1) ∧
    (∀ n, 12 ≤ n → (c n : ℤ) = 2 * c (n - 6) - c (n - 12)) ∧
    mk (fun n => (c n : ℤ)) * (1 - X ^ 6) ^ 2 =
      1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4 + X ^ 5 + 5 * X ^ 6 - 2 * X ^ 7 -
        3 * X ^ 8 - 2 * X ^ 9 + X ^ 10 - X ^ 11 ∧
    (∀ n, c (2 * n + 1) = A130196 (n + 1)) ∧
    (∀ n, c (A047245 (n + 1)) = A052901 (n + 2)) ∧
    (∀ n, c (3 * n) + c (3 * n + 1) + c (3 * n + 2) = A047238 (n + 3)) := by
  refine ⟨divides, c_val, ?_, c_gf, odd_ident, rank_ident, triple_ident⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  rw [show m + 12 - 6 = m + 6 by omega, show m + 12 - 12 = m by omega]
  exact c_rec m

end D5.S1.Recurrence.Residue.OEISA267068Quotients
