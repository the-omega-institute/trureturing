/- GID: D5/S1/Recurrence/Residue/OEISA242926UnsignedLucasRow
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA242926UnsignedLucasRow
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic]
   utility: none
   digest: The unsigned Curtz row is u_n = (L_(n+1) - 1)/(n + 1) with its A242926 identities. -/

import D5.S1.Scale.Lucas
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-! The unsigned companion of Curtz's array (A189731, A242926) and its Lucas first row. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA242926UnsignedLucasRow

open D5.S1.Scale Finset

/-- The upper entries `Ut m d = U(m, m + d)` of the unsigned array: zero diagonal, seed
`U(m, m + 1) = 1 / (m + 1)`, and `U(m, n) = U(m, n - 1) + U(m + 1, n - 1)` for `n ≥ m + 2`. -/
def Ut : ℕ → ℕ → ℚ
  | _, 0 => 0
  | m, 1 => 1 / (m + 1)
  | m, k + 2 => Ut m (k + 1) + Ut (m + 1) k

/-- The full unsigned square array: `U m n = Ut m (n - m)` for `m ≤ n` and the lower branch
`U m n = U (m - 1) (n + 1) - U (m - 1) n` for `m > n`. -/
def U : ℕ → ℕ → ℚ
  | 0, n => Ut 0 n
  | m + 1, n => if m + 1 ≤ n then Ut (m + 1) (n - (m + 1)) else U m (n + 1) - U m n

/-- The unsigned first row `u_n = U(0, n)`. -/
def u (n : ℕ) : ℚ := Ut 0 n

/-- A175385(n): the reduced numerator of `∑_{i=1}^{n} C(2n - i - 1, i - 1) / i`. -/
def A175385 (n : ℕ) : ℤ :=
  (∑ i ∈ Icc 1 n, ((2 * n - i - 1).choose (i - 1) : ℚ) / i).num

/-- A175386(n): the reduced denominator of `∑_{i=1}^{n} C(2n - i - 1, i - 1) / i`. -/
def A175386 (n : ℕ) : ℕ :=
  (∑ i ∈ Icc 1 n, ((2 * n - i - 1).choose (i - 1) : ℚ) / i).den

private def G (m e : ℕ) : ℚ := ∑ j ∈ range (e + 1), ((e - j).choose j : ℚ) / (m + j + 1)

private theorem G_rec (m e : ℕ) : G m (e + 2) = G m (e + 1) + G (m + 1) e := by
  let f : ℕ → ℚ := fun j => ((e + 2 - j).choose j : ℕ) / ((m : ℚ) + (j : ℕ) + 1)
  let g : ℕ → ℚ := fun j => ((e + 1 - j).choose j : ℕ) / ((m : ℚ) + (j : ℕ) + 1)
  let k : ℕ → ℚ := fun j => ((e - j).choose j : ℕ) / (((m + 1 : ℕ) : ℚ) + (j : ℕ) + 1)
  have hL : G m (e + 2) = (∑ i ∈ range (e + 1), f (i + 1)) + f (e + 2) + f 0 := by
    show ∑ j ∈ range (e + 2 + 1), f j = _
    rw [sum_range_succ', sum_range_succ]
  have hR : G m (e + 1) = (∑ i ∈ range (e + 1), g (i + 1)) + g 0 := by
    show ∑ j ∈ range (e + 1 + 1), g j = _
    rw [sum_range_succ']
  have hK : G (m + 1) e = ∑ i ∈ range (e + 1), k i := rfl
  have hlast : f (e + 2) = 0 := by
    simp only [f, show e + 2 - (e + 2) = 0 by omega,
      Nat.choose_eq_zero_of_lt (show 0 < e + 2 by omega)]
    simp
  have h0 : f 0 = g 0 := by simp [f, g]
  have hmid : ∀ i ∈ range (e + 1), f (i + 1) = g (i + 1) + k i := by
    intro i hi
    have hi' : i ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [f, g, k]
    rw [show e + 2 - (i + 1) = (e - i) + 1 by omega, show e + 1 - (i + 1) = e - i by omega,
      Nat.choose_succ_succ']
    push_cast
    ring
  rw [hL, hR, hK, hlast, h0, sum_congr rfl hmid, sum_add_distrib]
  ring

private theorem Ut_eq (e : ℕ) : ∀ m, Ut m (e + 1) = G m e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro m
    rcases e with _ | _ | e
    · simp [Ut, G]
    · simp [Ut, G, sum_range_succ]
    · rw [show e + 1 + 1 + 1 = (e + 1) + 2 by ring, Ut, ih (e + 1) (by omega) m,
        ih e (by omega) (m + 1), G_rec]

private theorem fib_sum (N : ℕ) :
    ∑ k ∈ range (N + 1), ((N - k).choose k : ℚ) = Nat.fib (N + 1) := by
  rw [Nat.fib_succ_eq_sum_choose, ← Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  rfl

private theorem u_lucas (n : ℕ) : u n = ((goldenLucas (n + 1) : ℚ) - 1) / (n + 1) := by
  rcases n with _ | e
  · simp [u, Ut, golden_lucas_succ_eq_fib_add_fib]
  rw [u, Ut_eq, G, eq_div_iff (by positivity), sum_mul]
  have hterm : ∀ j ∈ range (e + 1), ((e - j).choose j : ℚ) / ((0 : ℕ) + j + 1) *
      ((e + 1 : ℕ) + 1) = ((e + 1 - j).choose (j + 1) : ℚ) + ((e - j).choose j : ℚ) := by
    intro j hj
    have hj' : j ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have h := Nat.add_one_mul_choose_eq (e - j) j
    rw [show e - j + 1 = e + 1 - j by omega] at h
    have h' : ((e + 1 - j : ℕ) : ℚ) * ((e - j).choose j : ℚ) =
        ((e + 1 - j).choose (j + 1) : ℚ) * (j + 1) := by exact_mod_cast h
    rw [Nat.cast_sub (by omega)] at h'
    push_cast at h' ⊢
    field_simp
    linear_combination h'
  rw [sum_congr rfl hterm, sum_add_distrib]
  have h1 : ∑ j ∈ range (e + 1), ((e + 1 - j).choose (j + 1) : ℚ) = Nat.fib (e + 3) - 1 := by
    have := fib_sum (e + 2)
    rw [sum_range_succ, sum_range_succ'] at this
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one] at this
    rw [Nat.choose_eq_zero_of_lt (by omega : 0 < e + 2)] at this
    rw [← this]
    simp only [show ∀ j, e + 2 - (j + 1) = e + 1 - j from fun j => by omega]
    push_cast
    ring
  have h2 := fib_sum e
  rw [h1, h2, golden_lucas_succ_eq_fib_add_fib (e + 1), Nat.fib_add_two (n := e + 1)]
  push_cast
  ring

private theorem U_upper (m n : ℕ) (h : m ≤ n) : U m n = Ut m (n - m) := by
  cases m with
  | zero => simp [U]
  | succ m => simp [U, h]

private theorem U_lower (m n : ℕ) (h : n < m + 1) : U (m + 1) n = U m (n + 1) - U m n := by
  simp [U, show ¬ (m + 1 ≤ n) by omega]

private theorem U_diag (m : ℕ) : U m m = 0 := by
  rw [U_upper m m le_rfl, Nat.sub_self]; simp [Ut]

private theorem U_diff (m n : ℕ) : U (m + 1) n = U m (n + 1) - U m n := by
  rcases Nat.lt_or_ge n (m + 1) with h | h
  · exact U_lower m n h
  · obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - (m + 1), by omega⟩
    rw [U_upper _ _ (by omega), U_upper _ _ (by omega), U_upper _ _ (by omega),
      show m + 1 + d + 1 - m = d + 2 by omega, show m + 1 + d - m = d + 1 by omega,
      show m + 1 + d - (m + 1) = d by omega, Ut]
    ring

private theorem U_upper_rec (n m : ℕ) (h : n < m) : U n (m + 1) = U n m + U (n + 1) m := by
  rw [U_upper _ _ (by omega), U_upper _ _ (by omega), U_upper _ _ (by omega)]
  obtain ⟨d, rfl⟩ : ∃ d, m = n + 1 + d := ⟨m - (n + 1), by omega⟩
  rw [show n + 1 + d + 1 - n = d + 2 by omega, show n + 1 + d - n = d + 1 by omega,
    show n + 1 + d - (n + 1) = d by omega, Ut]

private theorem reflection_lower : ∀ m n, n ≤ m → U m n = (-1) ^ (m + n + 1) * U n m := by
  intro m
  induction m with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp [U_diag]
  | succ m ih =>
    intro n hn
    rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h; simp [U_diag]
    · rw [U_lower m n h]
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with h' | h'
      · subst h'
        rw [U_diag, show n + 1 + n + 1 = 2 * (n + 1) by ring, pow_mul]
        simp
      · rw [ih (n + 1) (by omega), ih n (by omega), U_upper_rec n m h']
        rw [show m + (n + 1) + 1 = (m + n + 1) + 1 by ring,
          show m + 1 + n + 1 = (m + n + 1) + 1 by ring, pow_succ]
        ring

private theorem reflection (m n : ℕ) : U m n = (-1) ^ (m + n + 1) * U n m := by
  rcases le_total n m with h | h
  · exact reflection_lower m n h
  · rw [reflection_lower n m h, ← mul_assoc, ← pow_add,
      show m + n + 1 + (n + m + 1) = 2 * (m + n + 1) by ring, pow_mul]
    simp

private theorem U_iter (m : ℕ) : U m = (fwdDiff 1)^[m] (U 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih]
    funext n
    simp [fwdDiff, U_diff]

private theorem inv_binomial (n : ℕ) :
    ∑ j ∈ range (n + 1), (-1) ^ (n - j) * (n.choose j : ℚ) * u j = (-1) ^ (n + 1) * u n := by
  have h := congrFun (U_iter n) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  have h2 := reflection n 0
  rw [h] at h2
  simp only [zsmul_eq_mul, zero_add, Nat.add_zero] at h2
  simpa [u, U, mul_comm, mul_left_comm, mul_assoc] using h2

private theorem anti_Ut (k : ℕ) : ∀ a, Ut a (2 * k + 2) =
    ∑ i ∈ range (k + 1), Ut (a + i) (2 * k + 1 - 2 * i) := by
  induction k with
  | zero => intro a; simp [Ut]
  | succ k ih =>
    intro a
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring, Ut, ih (a + 1), sum_range_succ' _ (k + 1)]
    simp only [show ∀ i, 2 * (k + 1) + 1 - 2 * (i + 1) = 2 * k + 1 - 2 * i from fun i => by omega,
      show ∀ i, a + 1 + i = a + (i + 1) from fun i => by omega]
    rw [show 2 * k + 2 + 1 = 2 * (k + 1) + 1 - 2 * 0 by omega, Nat.add_zero]
    ring_nf

private theorem antidiagonal (r : ℕ) :
    ∑ m ∈ range (r + 1), U m (2 * r + 1 - m) = u (2 * r + 2) := by
  rw [u, anti_Ut r 0]
  apply sum_congr rfl
  intro m hm
  have hm' : m ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [U_upper _ _ (by omega), zero_add, show 2 * r + 1 - m - m = 2 * r + 1 - 2 * m by omega]

private theorem odd_eq (r : ℕ) : u (2 * r + 1) =
    ∑ i ∈ Icc 1 (r + 1), ((2 * (r + 1) - i - 1).choose (i - 1) : ℚ) / i := by
  rw [u, Ut_eq, G]
  have htr : ∑ j ∈ range (2 * r + 1), ((2 * r - j).choose j : ℚ) / ((0 : ℕ) + j + 1) =
      ∑ j ∈ range (r + 1), ((2 * r - j).choose j : ℚ) / ((0 : ℕ) + j + 1) := by
    symm
    apply sum_subset
    · intro j hj; simp only [mem_range] at *; omega
    · intro j hj hj'
      simp only [mem_range, not_lt] at hj hj'
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [htr, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  apply sum_congr (by simp)
  intro j hj
  rw [show 2 * (r + 1) - (1 + j) - 1 = 2 * r - j by omega, show 1 + j - 1 = j by omega]
  push_cast
  ring

private theorem shift_fails : (u (2 * 1 + 1)).den ≠ A175386 1 := by
  have h1 : u (2 * 1 + 1) = 3 / 2 := by
    rw [u_lucas, show 2 * 1 + 1 + 1 = 3 + 1 by rfl, golden_lucas_succ_eq_fib_add_fib]
    norm_num [Nat.fib_add_two]
  have h2 : A175386 1 = 1 := by simp [A175386]
  rw [h1, h2]
  have h := Rat.den_div_eq_of_coprime (a := 3) (b := 2) (by norm_num) (by decide)
  push_cast at h
  omega

/-- Corollary 9 for the unsigned seed (A189731, A242926): the array agrees with its upper
entries; `u_n = (L_{n+1} - 1) / (n + 1)` with Lucas numbers `L`; the odd-index reduced numerators
and denominators are A175385 and A175386 at `r + 1`, while the unshifted index fails at `r = 1`;
the inverse binomial identity; and the upper antidiagonal sums equal `u_{2r+2}`. -/
theorem result :
    (∀ m d, U m (m + d) = Ut m d) ∧
    (∀ n, u n = ((goldenLucas (n + 1) : ℚ) - 1) / (n + 1)) ∧
    (∀ r, (u (2 * r + 1)).num = A175385 (r + 1) ∧ (u (2 * r + 1)).den = A175386 (r + 1)) ∧
    (u (2 * 1 + 1)).den ≠ A175386 1 ∧
    (∀ n, ∑ j ∈ range (n + 1), (-1) ^ (n - j) * (n.choose j : ℚ) * u j =
      (-1) ^ (n + 1) * u n) ∧
    (∀ r, ∑ m ∈ range (r + 1), U m (2 * r + 1 - m) = u (2 * r + 2)) := by
  refine ⟨fun m d => by rw [U_upper m (m + d) (by omega), Nat.add_sub_cancel_left], u_lucas,
    fun r => ⟨?_, ?_⟩, shift_fails, inv_binomial, antidiagonal⟩
  · rw [odd_eq]; rfl
  · rw [odd_eq]; rfl

end D5.S1.Recurrence.Residue.OEISA242926UnsignedLucasRow
