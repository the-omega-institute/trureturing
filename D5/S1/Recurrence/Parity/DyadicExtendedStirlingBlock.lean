/- GID: D5/S1/Recurrence/Parity/DyadicExtendedStirlingBlock
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/DyadicExtendedStirlingBlock
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The literal rational extended Stirling recurrence has an exact dyadic block formula. -/

import Mathlib.Tactic

/-! The dyadic block formula for the scalar rational recurrence A358612. -/

namespace D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The literal scalar recurrence for A358612 on positive columns.
Column zero is separately totalized to zero; source-domain calls never use it.
The recursion decreases the row first, then the column. -/
def T (n k : ℕ) : ℚ :=
  if k = 0 then 0 else
  if k = 1 then 1 else
  if n = 0 then (if k = 2 then 1 else 0) else
  (k : ℚ) * T (n / 2) k + T (n / 2) (k - 1) -
    if n % 2 = 0 then (T n (k - 1) + T (n / 2) (k - 1)) / ((k : ℚ) - 1) else 0
termination_by (n, k)
decreasing_by
  all_goals omega

private theorem T_one (n : ℕ) : T n 1 = 1 := by
  rw [T]
  simp

private theorem T_odd (m k : ℕ) (hk : 2 ≤ k) :
    T (2 * m + 1) k = (k : ℚ) * T m k + T m (k - 1) := by
  rw [T]
  simp [show k ≠ 0 by omega, show k ≠ 1 by omega, Nat.add_div]

private theorem T_even (m k : ℕ) (hm : 0 < m) (hk : 2 ≤ k) :
    T (2 * m) k = (k : ℚ) * T m k + T m (k - 1) -
      (T (2 * m) (k - 1) + T m (k - 1)) / ((k : ℚ) - 1) := by
  rw [T]
  simp [show k ≠ 0 by omega, show k ≠ 1 by omega,
    show 2 * m ≠ 0 by omega]

private theorem block (r h k : ℕ) (hk : 2 ≤ k) :
    T (2 ^ r * (2 * h + 1)) k =
      ((k : ℚ) - 1) ^ r * T h (k - 1) + (k : ℚ) ^ (r + 1) * T h k := by
  induction r generalizing k with
  | zero => simpa [add_comm] using T_odd h k hk
  | succ r ih =>
    have hm : 0 < 2 ^ r * (2 * h + 1) := by positivity
    have row : 2 ^ (r + 1) * (2 * h + 1) = 2 * (2 ^ r * (2 * h + 1)) := by ring
    rw [row]
    induction k, hk using Nat.le_induction with
    | base =>
      rw [T_even _ 2 hm (by omega), ih 2 (by omega)]
      norm_num [T_one]
      ring
    | succ k hk ikh =>
      have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      rw [T_even _ (k + 1) hm (by omega), ih (k + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih k hk, ikh]
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [add_sub_cancel_right, pow_succ]
      field_simp [hkq]
      <;> ring

/-- The exponent of the highest power of two dividing a positive row index. -/
def g (n : ℕ) : ℕ := padicValNat 2 n

/-- The exact natural quotient identifying the parent of a positive row. -/
def h (n : ℕ) : ℕ := (n / 2 ^ g n - 1) / 2

theorem dyadic_index (n : ℕ) (hn : 0 < n) :
    n = 2 ^ g n * (2 * h n + 1) := by
  have hp : 0 < 2 ^ g n := by positivity
  have heq : 2 ^ g n * Nat.divMaxPow n 2 = n := Nat.pow_padicValNat_mul_divMaxPow 2 n
  have hd : n / 2 ^ g n = Nat.divMaxPow n 2 := by
    calc
      n / 2 ^ g n = (2 ^ g n * Nat.divMaxPow n 2) / 2 ^ g n :=
        congrArg (fun x : ℕ => x / 2 ^ g n) heq.symm
      _ = Nat.divMaxPow n 2 := Nat.mul_div_right _ hp
  have hodd : ¬ 2 ∣ Nat.divMaxPow n 2 := Nat.not_dvd_divMaxPow (by omega) (by omega)
  have hmod : Nat.divMaxPow n 2 % 2 = 1 := by omega
  have hind : 2 * ((Nat.divMaxPow n 2 - 1) / 2) + 1 = Nat.divMaxPow n 2 := by omega
  unfold h
  rw [hd, hind]
  exact heq.symm

/-- The full unbounded A358612 block identity for the literal rational array. -/
theorem dyadic_extended_stirling_block (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    T n k = ((k : ℚ) - 1) ^ g n * T (h n) (k - 1) +
      (k : ℚ) ^ (g n + 1) * T (h n) k := by
  have hi := block (g n) (h n) k hk
  rw [← dyadic_index n hn] at hi
  exact hi

end D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
