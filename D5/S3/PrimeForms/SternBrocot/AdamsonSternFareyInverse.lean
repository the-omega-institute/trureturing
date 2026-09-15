/- GID: D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse
   generality: G
   mirror-B: D5/B/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Stern values invert the next Farey numerator modulo its denominator. -/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.SternBrocot.AdamsonSternFareyInverse

/-- Stern's scalar recursion, with explicit values at 0 and 1. -/
def stern (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n % 2 = 0 then stern (n / 2)
  else stern (n / 2) + stern (n / 2 + 1)
termination_by n

/-- Add numerator and denominator coordinates of adjacent fractions. -/
def mediant (a b : ℕ × ℕ) : ℕ × ℕ := (a.1 + b.1, a.2 + b.2)

/-- Full mediant row, on the valid indices 0,...,2^m.
The refinement copies even positions and inserts mediants at odd positions. -/
def fareyRow : ℕ → ℕ → ℕ × ℕ
  | 0, j => if j = 0 then (0, 1) else (1, 1)
  | m + 1, j =>
    if j % 2 = 0 then fareyRow m (j / 2)
    else mediant (fareyRow m (j / 2)) (fareyRow m (j / 2 + 1))

/-- Breadth-first listing in [0,1], with initial entries 0/1 and 1/1.
For r=2^m+j (1<=j<=2^m), select the (j-1)-th new mediant at level m. -/
def fareyEntry (r : ℕ) : ℕ × ℕ :=
  if r = 0 then (0, 1)
  else if r = 1 then (1, 1)
  else
    let m := Nat.log 2 (r - 1)
    let k := r - 1 - 2 ^ m
    fareyRow (m + 1) (2 * k + 1)

def fareyNum (r : ℕ) : ℕ := (fareyEntry r).1

def fareyDen (r : ℕ) : ℕ := (fareyEntry r).2

/-- Coordinates of every element of a full mediant row. -/
private theorem row_coordinates (m k : ℕ) (hk : k ≤ 2 ^ m) :
    fareyRow m k = (stern k, stern (2 ^ m + k)) := by
  have stern_zero : stern 0 = 0 := by
    rw [stern]
    norm_num
  have stern_one : stern 1 = 1 := by
    rw [stern]
    norm_num
  have stern_even (n : ℕ) : stern (2 * n) = stern n := by
    by_cases hn : n = 0
    · subst n
      simp
    · rw [stern, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      congr 1
      omega
  have stern_odd (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
    by_cases hn : n = 0
    · subst n
      simp [stern_zero, stern_one]
    · rw [stern, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hd : (2 * n + 1) / 2 = n := by omega
      rw [hd]
  induction m generalizing k with
  | zero =>
      have hk' : k = 0 ∨ k = 1 := by norm_num at hk; omega
      rcases hk' with rfl | rfl
      · norm_num [fareyRow, stern_zero, stern_one]
      · norm_num [fareyRow, stern_one]
        simpa [stern_one] using (stern_even 1).symm
  | succ m ih =>
      by_cases he : k % 2 = 0
      · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i := ⟨k / 2, by omega⟩
        have hi : i ≤ 2 ^ m := by rw [pow_succ] at hk; omega
        have hd : 2 * i / 2 = i := by omega
        rw [fareyRow, if_pos he, hd, ih i hi, stern_even]
        rw [show 2 ^ (m + 1) + 2 * i = 2 * (2 ^ m + i) by
          rw [pow_succ]; omega, stern_even]
      · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
        have hi : i + 1 ≤ 2 ^ m := by rw [pow_succ] at hk; omega
        have hd : (2 * i + 1) / 2 = i := by omega
        rw [fareyRow, if_neg he, hd, ih i (by omega), ih (i + 1) hi]
        simp only [mediant, stern_odd]
        rw [show 2 ^ (m + 1) + (2 * i + 1) = 2 * (2 ^ m + i) + 1 by
          rw [pow_succ]; omega, stern_odd]
        simp [Nat.add_assoc]


/-- Adjacent Stern columns at every dyadic level have determinant one. -/
private theorem stern_determinant (m k : ℕ) (hk : k < 2 ^ m) :
    stern (k + 1) * stern (2 ^ m + k) =
      stern k * stern (2 ^ m + k + 1) + 1 := by
  have stern_zero : stern 0 = 0 := by
    rw [stern]
    norm_num
  have stern_one : stern 1 = 1 := by
    rw [stern]
    norm_num
  have stern_even (n : ℕ) : stern (2 * n) = stern n := by
    by_cases hn : n = 0
    · subst n
      simp
    · rw [stern, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      congr 1
      omega
  have stern_odd (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
    by_cases hn : n = 0
    · subst n
      simp [stern_zero, stern_one]
    · rw [stern, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hd : (2 * n + 1) / 2 = n := by omega
      rw [hd]
  induction m generalizing k with
  | zero =>
      have hk0 : k = 0 := by norm_num at hk; omega
      subst k
      simp [stern_zero, stern_one]
  | succ m ih =>
      by_cases he : k % 2 = 0
      · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i := ⟨k / 2, by omega⟩
        have hi : i < 2 ^ m := by rw [pow_succ] at hk; omega
        have h := ih i hi
        rw [show 2 ^ (m + 1) + 2 * i = 2 * (2 ^ m + i) by
          rw [pow_succ]; omega]
        rw [stern_odd, stern_even, stern_even, stern_odd]
        nlinarith
      · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
        have hi : i < 2 ^ m := by rw [pow_succ] at hk; omega
        have h := ih i hi
        rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
        rw [show 2 ^ (m + 1) + (2 * i + 1) = 2 * (2 ^ m + i) + 1 by
          rw [pow_succ]; omega]
        rw [show 2 * (2 ^ m + i) + 1 + 1 = 2 * (2 ^ m + i + 1) by omega]
        rw [stern_even, stern_odd, stern_odd, stern_even]
        nlinarith


/-- Adamson's inverse claim for the supplied level-by-level Farey enumeration. -/
theorem result (n : ℕ) (hn : 0 < n) :
    stern n * fareyNum (n + 1) % fareyDen (n + 1) = 1 % fareyDen (n + 1) := by
  have stern_zero : stern 0 = 0 := by
    rw [stern]
    norm_num
  have stern_one : stern 1 = 1 := by
    rw [stern]
    norm_num
  have stern_odd (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
    by_cases hn : n = 0
    · subst n
      simp [stern_zero, stern_one]
    · rw [stern, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hd : (2 * n + 1) / 2 = n := by omega
      rw [hd]
  let m := Nat.log 2 n
  let k := n - 2 ^ m
  have hlo : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hk : k < 2 ^ m := by
    dsimp [k]
    rw [pow_succ] at hhi
    omega
  have hnk : n = 2 ^ m + k := by dsimp [k]; omega
  have hentry : fareyEntry (n + 1) = (stern (2 * k + 1), stern (2 * n + 1)) := by
    simp only [fareyEntry, if_neg (show n + 1 ≠ 0 by omega),
      if_neg (show n + 1 ≠ 1 by omega), Nat.add_sub_cancel]
    change fareyRow (m + 1) (2 * k + 1) = _
    rw [row_coordinates (m + 1) (2 * k + 1) (by rw [pow_succ]; omega)]
    congr 2
    rw [pow_succ]
    omega
  have hdet := stern_determinant m k hk
  rw [← hnk] at hdet
  have hproduct : stern n * (stern k + stern (k + 1)) =
      stern k * (stern n + stern (n + 1)) + 1 := by
    nlinarith
  change stern n * (fareyEntry (n + 1)).1 % (fareyEntry (n + 1)).2 =
    1 % (fareyEntry (n + 1)).2
  rw [hentry]
  simp only [stern_odd]
  rw [hproduct]
  simp [Nat.add_mod]

end D5.S3.PrimeForms.SternBrocot.AdamsonSternFareyInverse
