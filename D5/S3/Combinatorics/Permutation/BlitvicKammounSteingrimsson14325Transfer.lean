/- GID: D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Universal modular invariants of the overlap-two grid transfer. -/

import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
The row index is zero-based: `row R n k` denotes b_(n+1)(k).
These are algebraically defined transfer rows, not the actual packing count.
The missing insertion/deletion correspondence must identify A(j) with
`row ℕ (j-1) 3` before their residues apply to the source permutations.
Escape audits: https://github.com/the-omega-institute/trureturing/issues/28504.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer

open scoped BigOperators

/-- The sum from r=1 to k, with summation variable shifted down by one. -/
def transfer {R : Type*} [Semiring R] (f : ℕ → R) (k : ℕ) : R :=
  ∑ r ∈ Finset.range k, (r + 1 : R) * f (r + 3)

/-- The initial row is constant one, including auxiliary arguments below three. -/
def row (R : Type*) [Semiring R] : ℕ → ℕ → R
  | 0, _ => 1
  | n + 1, k => transfer (row R n) k

private theorem transfer_succ {R : Type*} [Semiring R] (f : ℕ → R) (k : ℕ) :
    transfer f (k + 1) = transfer f k + (k + 1 : R) * f (k + 3) := by
  exact Finset.sum_range_succ _ _

private def firstProfile (k : ℕ) : ZMod 5 :=
  ![0, 1, 3, 1, 0] ⟨k % 5, Nat.mod_lt _ (by decide)⟩

private def stableProfile (k : ℕ) : ZMod 5 :=
  ![0, 1, 1, 1, 0] ⟨k % 5, Nat.mod_lt _ (by decide)⟩

private theorem profile_steps (k : ℕ) :
    firstProfile (k + 1) = firstProfile k + (k + 1 : ZMod 5) ∧
    stableProfile (k + 1) = stableProfile k +
      (k + 1 : ZMod 5) * firstProfile (k + 3) ∧
    stableProfile (k + 1) = stableProfile k +
      (k + 1 : ZMod 5) * stableProfile (k + 3) := by
  have hc : (k : ZMod 5) = (k % 5 : ℕ) := by simp
  have hk := Nat.mod_lt k (by decide : 0 < 5)
  interval_cases h : k % 5 <;>
    norm_num [firstProfile, stableProfile, Nat.add_mod, h, Nat.cast_add, hc] <;>
    decide +kernel

private theorem transfer_one : transfer (fun _ => (1 : ZMod 5)) = firstProfile := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transfer_succ, ih, mul_one]
    exact (profile_steps k).1.symm

private theorem transfer_first : transfer firstProfile = stableProfile := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transfer_succ, ih]
    exact (profile_steps k).2.1.symm

private theorem transfer_stable : transfer stableProfile = stableProfile := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transfer_succ, ih]
    exact (profile_steps k).2.2.symm

private theorem rows_stabilize (n : ℕ) : row (ZMod 5) (n + 2) = stableProfile := by
  induction n with
  | zero => exact (congrArg transfer transfer_one).trans transfer_first
  | succ n ih =>
    change transfer (row (ZMod 5) (n + 2)) = stableProfile
    rw [ih, transfer_stable]

/-- Every transfer row has residue one at the source's argument three. -/
theorem row_mod_five (n : ℕ) : row (ZMod 5) n 3 = 1 := by
  rcases n with _ | _ | n
  · rfl
  · exact congrFun transfer_one 3
  · rw [rows_stabilize]
    rfl

private theorem even_neighbor (n k : ℕ) :
    2 * row (ZMod 4) n (2 * k + 2) =
      2 * row (ZMod 4) n (2 * k + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
    change 2 * transfer (row (ZMod 4) n) (2 * k + 1 + 1) = _
    rw [transfer_succ]
    change 2 * (transfer (row (ZMod 4) n) (2 * k + 1) +
      ((2 * k + 1 : ℕ) + 1 : ZMod 4) * row (ZMod 4) n (2 * k + 1 + 3)) = _
    push_cast
    calc
      _ = 2 * transfer (row (ZMod 4) n) (2 * k + 1) +
          4 * ((k : ZMod 4) + 1) * row (ZMod 4) n (2 * k + 1 + 3) := by ring
      _ = _ := by rw [show (4 : ZMod 4) = 0 by decide]; simp only [row]; ring

private theorem even_weight (n k : ℕ) :
    ((2 * k + 2 : ℕ) : ZMod 4) * row (ZMod 4) n (2 * k + 4) =
      -((2 * k + 2 : ℕ) : ZMod 4) * row (ZMod 4) n (2 * k + 3) := by
  have he := even_neighbor n (k + 1)
  have hleft : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  have hright : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [hleft, hright] at he
  calc
    _ = ((k : ZMod 4) + 1) * (2 * row (ZMod 4) n (2 * k + 4)) := by push_cast; ring
    _ = ((k : ZMod 4) + 1) * (2 * row (ZMod 4) n (2 * k + 3)) := by rw [he]
    _ = _ := by
      rw [show (2 : ZMod 4) = -2 by decide]
      push_cast
      ring

/-- Odd arguments satisfy the reduced recurrence over Z/4, including k=0. -/
theorem odd_row_recurrence (n k : ℕ) :
    row (ZMod 4) (n + 1) (2 * k + 1) =
      -(∑ r ∈ Finset.range k, row (ZMod 4) n (2 * r + 3)) +
        ((2 * k + 1 : ℕ) : ZMod 4) * row (ZMod 4) n (2 * k + 3) := by
  induction k with
  | zero => simp [row, transfer]
  | succ k ih =>
    change transfer (row (ZMod 4) n) (2 * (k + 1) + 1) = _
    have hi : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
    rw [hi, transfer_succ, transfer_succ]
    simp only [← Nat.cast_add_one]
    change row (ZMod 4) (n + 1) (2 * k + 1) +
      ((2 * k + 2 : ℕ) : ZMod 4) * row (ZMod 4) n (2 * k + 4) +
      ((2 * k + 3 : ℕ) : ZMod 4) * row (ZMod 4) n (2 * k + 5) = _
    rw [ih, even_weight, Finset.sum_range_succ]
    have hj : 2 * (k + 1) + 3 = 2 * k + 5 := by omega
    rw [hj]
    push_cast
    ring

open PowerSeries

private noncomputable def cat : PowerSeries (ZMod 4) :=
  PowerSeries.catalanSeries.map (Nat.castRingHom (ZMod 4))

private theorem cat_equation : cat = 1 + X * cat ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom (ZMod 4)))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simpa [cat, mul_comm, add_comm] using h.symm

private noncomputable def V : PowerSeries (ZMod 4) := 3 * cat ^ 2 - 2
private noncomputable def U : PowerSeries (ZMod 4) := 1 + X * V

private theorem V_equation : V + 2 * X * V + X ^ 2 * V ^ 2 = 1 := by
  have h : cat ^ 2 = 1 + 2 * X * cat ^ 2 + X ^ 2 * cat ^ 4 := by
    calc
      cat ^ 2 = (1 + X * cat ^ 2) ^ 2 := congrArg (fun f => f ^ 2) cat_equation
      _ = _ := by ring
  dsimp [V]
  linear_combination 3 * h

private theorem U_V_equations :
    U = (1 + 2 * X) * V + X * U * V ∧ V = U * V - X * V ^ 2 := by
  constructor
  · dsimp [U]
    linear_combination -V_equation
  · dsimp [U]; ring

private noncomputable def oddSeries (k : ℕ) : PowerSeries (ZMod 4) :=
  if k % 2 = 0 then U * V ^ (k / 2) else V ^ (k / 2 + 1)

private theorem oddSeries_even (k : ℕ) : oddSeries (2 * k) = U * V ^ k := by
  simp [oddSeries]

private theorem oddSeries_odd (k : ℕ) : oddSeries (2 * k + 1) = V ^ (k + 1) := by
  have hd : (2 * k + 1) / 2 = k := by omega
  simp [oddSeries, hd, Nat.add_mod]

private theorem oddSeries_adjacent (k : ℕ) :
    oddSeries k = (1 + (2 * k + 2 : ℕ) * X) * oddSeries (k + 1) -
      (2 * k + 3 : ℕ) * X * oddSeries (k + 2) := by
  have he : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  obtain ⟨hU, hV⟩ := U_V_equations
  rcases he with he | he
  · generalize k / 2 = m at he
    subst k
    rw [oddSeries_even, oddSeries_odd, show 2 * m + 2 = 2 * (m + 1) by omega,
      oddSeries_even, pow_succ]
    have h2 : ((2 * (2 * m) + 2 : ℕ) : PowerSeries (ZMod 4)) = 2 := by
      push_cast; ring
    have h3 : ((2 * (2 * m) + 3 : ℕ) : PowerSeries (ZMod 4)) = -1 := by
      push_cast; ring
    rw [h2, h3, hU]
    ring
  · generalize k / 2 = m at he
    subst k
    rw [oddSeries_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
      oddSeries_even, show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega,
      oddSeries_odd]
    have h2 : ((2 * (2 * m + 1) + 2 : ℕ) : PowerSeries (ZMod 4)) = 0 := by
      push_cast; ring
    have h3 : ((2 * (2 * m + 1) + 3 : ℕ) : PowerSeries (ZMod 4)) = 1 := by
      push_cast; ring
    rw [h2, h3, hV, pow_succ]
    ring

private theorem oddSeries_recurrence (k : ℕ) :
    oddSeries k = 1 + X *
      (-(∑ r ∈ Finset.range k, oddSeries (r + 1)) +
        (2 * k + 1 : ℕ) * oddSeries (k + 1)) := by
  induction k with
  | zero => simp [oddSeries, U]
  | succ k ih =>
    have ha := oddSeries_adjacent k
    rw [ih] at ha
    rw [Finset.sum_range_succ]
    push_cast at ha ⊢
    linear_combination ha

private theorem oddSeries_constant (k : ℕ) : constantCoeff (oddSeries k) = 1 := by
  have hc : constantCoeff cat = 1 := by simp [cat]
  have hv : constantCoeff V = 1 := by norm_num [V, hc]
  have hu : constantCoeff U = 1 := by simp [U]
  simp [oddSeries, hv, hu]

private theorem row_eq_oddSeries (n k : ℕ) :
    row (ZMod 4) n (2 * k + 1) = coeff n (oddSeries k) := by
  induction n generalizing k with
  | zero => simpa [row, coeff_zero_eq_constantCoeff] using (oddSeries_constant k).symm
  | succ n ih =>
    have h := congrArg (coeff (n + 1)) (oddSeries_recurrence k)
    simp only [map_add, coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
      coeff_succ_X_mul, map_neg, map_sum, coeff_natCast_mul] at h
    rw [odd_row_recurrence, h]
    simp only [ih]

/-- At every positive row index the source argument three is three times
    the next Catalan number modulo four. The initial row is separately one. -/
theorem row_catalan_mod_four (n : ℕ) :
    row (ZMod 4) (n + 1) 3 = 3 * (catalan (n + 2) : ZMod 4) := by
  have hr := row_eq_oddSeries (n + 1) 1
  have hc := congrArg (coeff (n + 2)) cat_equation
  simp only [map_add, coeff_one, show n + 2 ≠ 0 by omega, ↓reduceIte,
    zero_add, show n + 2 = (n + 1) + 1 by omega, coeff_succ_X_mul] at hc
  have hcat : coeff (n + 2) cat = (catalan (n + 2) : ZMod 4) := by simp [cat]
  rw [hcat] at hc
  simpa [oddSeries, V, map_sub, coeff_natCast_mul, ← hc] using hr

end D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer
