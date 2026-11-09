/- GID: D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Universal modular invariants of the overlap-two grid transfer. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
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
The Core module derives the insertion/deletion correspondence identifying A(j)
with `row ℕ (j-1) 3` and applies these residues to the source permutations.
Escape audits: https://github.com/the-omega-institute/trureturing/issues/28504.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer

open scoped BigOperators Classical

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
  have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C (R := ZMod 4)) (by decide : (4 : ZMod 4) = 0)
  have h12 : (12 : PowerSeries (ZMod 4)) = 0 := by linear_combination 3 * h4
  linear_combination (norm := (ring_nf; simp [h4, h12])) 3 * h

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
    oddSeries k = (1 + ((2 * k + 2 : ℕ) : PowerSeries (ZMod 4)) * X) * oddSeries (k + 1) -
      ((2 * k + 3 : ℕ) : PowerSeries (ZMod 4)) * X * oddSeries (k + 2) := by
  have he : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  obtain ⟨hU, hV⟩ := U_V_equations
  have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C (R := ZMod 4)) (by decide : (4 : ZMod 4) = 0)
  rcases he with he | he
  · generalize k / 2 = m at he
    subst k
    rw [oddSeries_even, oddSeries_odd, show 2 * m + 2 = 2 * (m + 1) by omega,
      oddSeries_even, pow_succ]
    have h2 : ((2 * (2 * m) + 2 : ℕ) : PowerSeries (ZMod 4)) = 2 := by
      push_cast
      linear_combination (norm := (ring_nf; simp [h4])) h4
    have h3 : ((2 * (2 * m) + 3 : ℕ) : PowerSeries (ZMod 4)) = -1 := by
      push_cast
      linear_combination (norm := (ring_nf; simp [h4])) h4
    rw [h2, h3]
    linear_combination V ^ m * hU
  · generalize k / 2 = m at he
    subst k
    rw [oddSeries_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
      oddSeries_even, show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega,
      oddSeries_odd]
    have h2 : ((2 * (2 * m + 1) + 2 : ℕ) : PowerSeries (ZMod 4)) = 0 := by
      push_cast
      linear_combination (norm := (ring_nf; simp [h4])) h4
    have h3 : ((2 * (2 * m + 1) + 3 : ℕ) : PowerSeries (ZMod 4)) = 1 := by
      push_cast
      linear_combination (norm := (ring_nf; simp [h4])) h4
    rw [h2, h3, pow_succ, pow_succ]
    linear_combination V ^ m * hV

private theorem oddSeries_recurrence (k : ℕ) :
    oddSeries k = 1 + X *
      (-(∑ r ∈ Finset.range k, oddSeries (r + 1)) +
        ((2 * k + 1 : ℕ) : PowerSeries (ZMod 4)) * oddSeries (k + 1)) := by
  induction k with
  | zero => simp [oddSeries, U]
  | succ k ih =>
    have ha := oddSeries_adjacent k
    rw [ih] at ha
    rw [Finset.sum_range_succ]
    push_cast at ha ⊢
    linear_combination -ha

private theorem oddSeries_constant (k : ℕ) : constantCoeff (oddSeries k) = 1 := by
  have hc : constantCoeff cat = 1 := by
    rw [← coeff_zero_eq_constantCoeff]; simp [cat]
  have hv : constantCoeff V = 1 := by
    simp only [V, map_sub, map_mul, map_pow, map_ofNat, hc, one_pow, mul_one]
    decide
  have hu : constantCoeff U = 1 := by simp [U]
  unfold oddSeries
  split_ifs <;> simp [map_pow, hv, hu]

private theorem row_eq_oddSeries (n k : ℕ) :
    row (ZMod 4) n (2 * k + 1) = coeff n (oddSeries k) := by
  induction n generalizing k with
  | zero => simpa [row, coeff_zero_eq_constantCoeff] using (oddSeries_constant k).symm
  | succ n ih =>
    have h := congrArg (coeff (n + 1)) (oddSeries_recurrence k)
    simp only [map_add, coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
      coeff_succ_X_mul, map_neg, map_sum, coeff_natCast_mul] at h
    have hi (r : ℕ) : row (ZMod 4) n (2 * r + 3) = coeff n (oddSeries (r + 1)) := by
      simpa only [show 2 * (r + 1) + 1 = 2 * r + 3 by omega] using ih (r + 1)
    rw [odd_row_recurrence, h]
    simp only [hi]

private theorem row_natCast {R : Type*} [Semiring R] (n k : ℕ) :
    (row ℕ n k : R) = row R n k := by
  induction n generalizing k with
  | zero => simp [row]
  | succ n ih => simp [row, transfer, Nat.cast_sum, Nat.cast_mul, ih]

/-- At every positive row index the source argument three is three times
    the next Catalan number modulo four. The initial row is separately one. -/
theorem row_catalan_mod_four (n : ℕ) :
    (row ℕ (n + 1) 3 : ZMod 4) = 3 * (catalan (n + 2) : ZMod 4) := by
  rw [row_natCast]
  have hr := row_eq_oddSeries (n + 1) 1
  have hc := congrArg (coeff (n + 2)) cat_equation
  simp only [map_add, coeff_one, show n + 2 ≠ 0 by omega, ↓reduceIte,
    zero_add, show n + 2 = (n + 1) + 1 by omega, coeff_succ_X_mul] at hc
  have hcat : coeff (n + 2) cat = (catalan (n + 2) : ZMod 4) := by simp [cat]
  rw [hcat] at hc
  simpa [oddSeries, V, map_sub, coeff_natCast_mul, ← hc,
    ← map_ofNat (C (R := ZMod 4)), coeff_C] using hr

private theorem row_parity (n : ℕ) :
    Odd (row ℕ n 3) ↔ ∃ k : ℕ, 1 ≤ k ∧ n + 2 = 2 ^ k := by
  cases n with
  | zero => simp [row]; exact ⟨1, by omega, by decide⟩
  | succ n =>
    have h := congrArg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2))
      (row_catalan_mod_four n)
    simp only [map_mul, map_ofNat, map_natCast] at h
    rw [show (3 : ZMod 2) = 1 by decide, one_mul] at h
    have hc := D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.binary_catalan (n + 3)
    have hb : (catalan (n + 2) : ZMod 2) = 1 ↔ ∃ k : ℕ, n + 3 = 2 ^ k := by
      simp only [D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries,
        D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanUnit,
        PowerSeries.coeff_map, PowerSeries.coeff_succ_X_mul,
        PowerSeries.catalanSeries_coeff] at hc
      change ((catalan (n + 2) : ℤ) : ZMod 2) = 1 ↔ ∃ k : ℕ, n + 3 = 2 ^ k at hc
      simpa only [Int.cast_natCast] using hc
    rw [← ZMod.natCast_eq_one_iff_odd, h, hb]
    change (∃ k : ℕ, n + 3 = 2 ^ k) ↔ ∃ k : ℕ, 1 ≤ k ∧ n + 3 = 2 ^ k
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_, hk⟩
      by_contra hn
      have hz : k = 0 := by omega
      simp [hz] at hk
    · rintro ⟨k, hk, he⟩
      exact ⟨k, he⟩

/-- The full dyadic modulo-ten rule for the algebraic natural transfer rows.
    Applying it to the source count still requires the grid-to-row bijection. -/
theorem row_mod_ten (n : ℕ) :
    row ℕ n 3 % 10 =
      if ∃ k : ℕ, 1 ≤ k ∧ n + 2 = 2 ^ k then 1 else 6 := by
  have h5 : row ℕ n 3 % 5 = 1 := by
    have h := (row_natCast n 3 (R := ZMod 5)).trans (row_mod_five n)
    exact (ZMod.natCast_eq_natCast_iff' _ 1 5).mp h
  have h2 : row ℕ n 3 % 2 = 1 ↔ ∃ k : ℕ, 1 ≤ k ∧ n + 2 = 2 ^ k := by
    rw [← row_parity, Nat.odd_iff]
  have h10 := Nat.mod_lt (row ℕ n 3) (by decide : 0 < 10)
  have hr5 : (row ℕ n 3 % 10) % 5 = 1 := by omega
  have hr2 : (row ℕ n 3 % 10) % 2 = row ℕ n 3 % 2 := by omega
  split_ifs with h
  · have := h2.mpr h
    omega
  · have hn : row ℕ n 3 % 2 ≠ 1 := mt h2.mp h
    omega

private def bitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private theorem bitSum_even (n : ℕ) : bitSum (2 * n) = bitSum n := by
  by_cases hn : n = 0
  · simp [hn, bitSum]
  · simp [bitSum, Nat.digits_base_mul (by decide : 1 < 2) (by omega : 0 < n)]

private theorem bitSum_odd (n : ℕ) : bitSum (2 * n + 1) = bitSum n + 1 := by
  unfold bitSum
  rw [show 2 * n + 1 = 1 + 2 * n by omega,
    show Nat.digits 2 (1 + 2 * n) = 1 :: Nat.digits 2 n from
      Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))]
  simp [bitSum, Nat.add_comm]

private theorem bitSum_pos (n : ℕ) (hn : 0 < n) : 0 < bitSum n := by
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 (by omega))⟩

private theorem bitSum_shift (k n : ℕ) (hn : 0 < n) : bitSum (2 ^ k * n) = bitSum n := by
  simp [bitSum, Nat.digits_base_pow_mul (by decide : 1 < 2) hn]

private theorem bitSum_pow (k : ℕ) : bitSum (2 ^ k) = 1 := by
  simpa [bitSum] using bitSum_shift k 1 (by decide)

private theorem bitSum_increment (n : ℕ) :
    bitSum (n + 1) + padicValNat 2 (n + 1) = bitSum n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n % 2 = 0
    · have hn : n = 2 * (n / 2) := by omega
      have hv : padicValNat 2 (n + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by
        intro hd
        have := Nat.mod_eq_zero_of_dvd hd
        omega)
      rw [hv, hn, bitSum_even, bitSum_odd, add_zero]
    · have hn : n = 2 * (n / 2) + 1 := by omega
      have hi := ih (n / 2) (by omega)
      have hv : padicValNat 2 (n + 1) = 1 + padicValNat 2 (n / 2 + 1) := by
        rw [show n + 1 = 2 * (n / 2 + 1) by omega,
          padicValNat.mul (by decide : 2 ≠ 0) (by omega), padicValNat_self]
      have hb : bitSum (n + 1) = bitSum (n / 2 + 1) := by
        rw [show n + 1 = 2 * (n / 2 + 1) by omega, bitSum_even]
      have hb0 : bitSum n = bitSum (n / 2) + 1 := by
        calc
          bitSum n = bitSum (2 * (n / 2) + 1) := congrArg bitSum hn
          _ = _ := bitSum_odd _
      rw [hv, hb, hb0]
      omega

private theorem bitSum_eq_one (n : ℕ) : bitSum n = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · intro hb
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases he : n % 2 = 0
      · have hn : n = 2 * (n / 2) := by omega
        have hp : 0 < n := by
          by_contra hnp
          have hz : n = 0 := by omega
          subst n
          norm_num [bitSum] at hb
        have hm := hb
        rw [hn, bitSum_even] at hm
        obtain ⟨k, hk⟩ := ih (n / 2) (by omega) hm
        exact ⟨k + 1, by rw [hn, hk, pow_succ]; omega⟩
      · have hn : n = 2 * (n / 2) + 1 := by omega
        have hm : bitSum (n / 2) = 0 := by rw [hn, bitSum_odd] at hb; omega
        have hz : n / 2 = 0 := by
          by_contra hz
          have := bitSum_pos (n / 2) (by omega)
          omega
        exact ⟨0, by simp; omega⟩
  · rintro ⟨k, rfl⟩
    exact bitSum_pow k

private theorem bitSum_le_two (n : ℕ) (hn : 2 ≤ n) :
    bitSum n ≤ 2 ↔ ∃ i p : ℕ, p ≤ i ∧ n = 2 ^ i + 2 ^ p := by
  constructor
  · intro hb
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn2 : n = 2
      · exact ⟨0, 0, by omega, by omega⟩
      by_cases he : n % 2 = 0
      · have hne : n = 2 * (n / 2) := by omega
        have hm := hb
        rw [hne, bitSum_even] at hm
        obtain ⟨i, p, hpi, hp⟩ := ih (n / 2) (by omega) (by omega) hm
        refine ⟨i + 1, p + 1, by omega, ?_⟩
        rw [hne, hp, pow_succ, pow_succ]
        omega
      · have hne : n = 2 * (n / 2) + 1 := by omega
        have hm : bitSum (n / 2) = 1 := by
          have hpos := bitSum_pos (n / 2) (by omega)
          rw [hne, bitSum_odd] at hb
          omega
        obtain ⟨k, hk⟩ := (bitSum_eq_one (n / 2)).mp hm
        refine ⟨k + 1, 0, by omega, ?_⟩
        rw [hne, hk, pow_succ]
        omega
  · rintro ⟨i, p, hpi, rfl⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpi
    cases d with
    | zero =>
      have he : 2 ^ (p + 0) + 2 ^ p = 2 ^ (p + 1) := by simp only [Nat.add_zero, pow_succ]; omega
      rw [he, bitSum_pow]
      decide
    | succ d =>
      have he : 2 ^ (p + (d + 1)) + 2 ^ p = 2 ^ p * (2 * 2 ^ d + 1) := by
        rw [pow_add, pow_succ]; ring
      rw [he, bitSum_shift p _ (by omega), bitSum_odd, bitSum_pow]

private theorem catalan_ne_zero (n : ℕ) : catalan n ≠ 0 := by
  intro hz
  have h := succ_mul_catalan_eq_centralBinom n
  rw [hz, mul_zero] at h
  exact Nat.centralBinom_ne_zero n h.symm

private theorem catalan_valuation (n : ℕ) :
    padicValNat 2 (catalan n) + 1 = bitSum (n + 1) := by
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p := 2) (k := n) (n := n)
  have hs : (Nat.digits 2 (n + n)).sum = bitSum n := by
    simpa only [bitSum, two_mul] using bitSum_even n
  have hcentral : padicValNat 2 n.centralBinom = bitSum n := by
    change (2 - 1) * padicValNat 2 ((n + n).choose n) = bitSum n + bitSum n - _ at h
    rw [hs] at h
    simpa [Nat.centralBinom, two_mul] using h
  have hp := congrArg (padicValNat 2) (succ_mul_catalan_eq_centralBinom n)
  rw [padicValNat.mul (by omega) (catalan_ne_zero n), hcentral] at hp
  have hi := bitSum_increment n
  omega

/-- Both directions of the two-power exception rule for natural transfer rows,
    including equal exponents and the exponent-zero boundary. -/
theorem row_mod_four_iff (n : ℕ) :
    (¬ 4 ∣ row ℕ n 3) ↔ ∃ i p : ℕ, p ≤ i ∧ n + 2 = 2 ^ i + 2 ^ p := by
  cases n with
  | zero =>
    constructor
    · intro _; exact ⟨0, 0, by omega, by decide⟩
    · intro _; change ¬ 4 ∣ 1; decide
  | succ n =>
    have hr := row_catalan_mod_four n
    have hz : (row ℕ (n + 1) 3 : ZMod 4) = 0 ↔ (catalan (n + 2) : ZMod 4) = 0 := by
      rw [hr]
      constructor
      · intro h
        have hh := congrArg (fun x : ZMod 4 => 3 * x) h
        simpa only [← mul_assoc, show (3 : ZMod 4) * 3 = 1 by decide,
          one_mul, mul_zero] using hh
      · intro h; rw [h, mul_zero]
    rw [← ZMod.natCast_eq_zero_iff, hz, ZMod.natCast_eq_zero_iff]
    have hv := catalan_valuation (n + 2)
    rw [show n + 2 + 1 = n + 1 + 2 by omega] at hv
    have hd : 4 ∣ catalan (n + 2) ↔ 2 ≤ padicValNat 2 (catalan (n + 2)) := by
      simpa using (padicValNat_dvd_iff_le (p := 2) (catalan_ne_zero (n + 2)) (n := 2))
    rw [hd, not_le]
    rw [← bitSum_le_two (n + 1 + 2) (by omega)]
    omega

end D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer
