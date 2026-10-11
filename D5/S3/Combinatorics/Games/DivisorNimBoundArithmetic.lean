/- GID: D5/S3/Combinatorics/Games/DivisorNimBoundArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimBoundArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer recurrence estimates for the distinguished-heap Divisor Nim bound. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

namespace D5.S3.Combinatorics.Games.DivisorNimBoundArithmetic

open scoped BigOperators

def coarseBound (k H : ℕ) : ℕ := (∑ j ∈ Finset.range (k + 1), H / 2 ^ j) + k + 1

def oddDivisorCount (u : ℕ) : ℕ := u.divisors.card

def changedBound (v u j : ℕ) : ℕ :=
  2 * (2 ^ v * u) - (2 ^ v * u) / 2 ^ j - 2 ^ (j + 1) + j + 2

def exceptionalCount (v u k : ℕ) : ℕ :=
  if k = v then u else (v - k + 1) * oddDivisorCount u

def recurrenceBound (v u : ℕ) : ℕ → ℕ
  | 0 => (v + 1) * oddDivisorCount u + 1
  | k + 1 => max (recurrenceBound v u k)
      ((Finset.range (k + 1)).sup (changedBound v u)) + exceptionalCount v u (k + 1) + 1

def bound (v u : ℕ) : ℕ := recurrenceBound v u v

theorem recurrenceBound_mono (v u : ℕ) : Monotone (recurrenceBound v u) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [recurrenceBound]
  exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))

theorem oddDivisorCount_le (u : ℕ) : oddDivisorCount u ≤ u := by
  have h : u.divisors ⊆ Finset.Icc 1 u := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd))
        (Nat.dvd_of_mem_divisors hd)⟩
  simpa [oddDivisorCount] using Finset.card_le_card h

theorem finite_bound (v u : ℕ) (hv : 1 ≤ v) (hv' : v ≤ 15)
    (hu : 1 ≤ u) (hu' : u ≤ v) (hodd : u % 2 = 1)
    (hex : ¬ (u = 1 ∧ v ≤ 3)) : bound v u ≤ 2 * 2 ^ v * u := by
  have hu15 : u ≤ 15 := hu'.trans hv'
  interval_cases v <;> interval_cases u <;> norm_num at *
  all_goals decide

def triangle (v : ℕ) : ℕ := v * (v + 1) / 2

theorem triangle_twice (v : ℕ) : 2 * triangle v = v * (v + 1) := by
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self v)

private def fifthPolynomial (v : ℕ) := v * (v * v + 5 * v + 2) ^ 2

private theorem fifthPolynomial_step (n : ℕ) :
    fifthPolynomial (n + 17) ≤ 2 * fifthPolynomial (n + 16) := by
  dsimp [fifthPolynomial]
  ring_nf
  omega

private theorem fifthPolynomial_le (n : ℕ) :
    fifthPolynomial (n + 16) ≤ 2 ^ (n + 21) := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      fifthPolynomial (n + 1 + 16) ≤ 2 * fifthPolynomial (n + 16) := by
        simpa [Nat.add_assoc] using fifthPolynomial_step n
      _ ≤ 2 * 2 ^ (n + 21) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1 + 21) := by
        rw [show n + 1 + 21 = (n + 21) + 1 by omega]
        exact (Nat.mul_comm _ _).trans (pow_succ 2 (n + 21)).symm

theorem large_exponential_square (v : ℕ) (hv : 16 ≤ v) :
    v * (triangle v + 2 * v + 1) ^ 2 ≤ 2 ^ (v + 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hv
  have hp := fifthPolynomial_le n
  have ha := triangle_twice (16 + n)
  have he : 2 ^ (n + 21) = 4 * 2 ^ (16 + n + 3) := by
    rw [show n + 21 = (16 + n + 3) + 2 by omega, pow_add]
    norm_num
    ring
  rw [he] at hp
  have hi : fifthPolynomial (n + 16) =
      4 * ((16 + n) * (triangle (16 + n) + 2 * (16 + n) + 1) ^ 2) := by
    dsimp [fifthPolynomial]
    have hx : (n + 16) * (n + 16) + 5 * (n + 16) + 2 =
        2 * (triangle (16 + n) + 2 * (16 + n) + 1) := by nlinarith
    rw [hx]
    ring
  rw [hi] at hp
  omega

private theorem quadratic_step (n : ℕ) :
    (n + 17) ^ 2 + 5 * (n + 17) + 4 ≤
      2 * ((n + 16) ^ 2 + 5 * (n + 16) + 4) := by
  ring_nf
  omega

private theorem quadratic_le (n : ℕ) :
    (n + 16) ^ 2 + 5 * (n + 16) + 4 ≤ 2 ^ (n + 18) := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      (n + 1 + 16) ^ 2 + 5 * (n + 1 + 16) + 4 ≤
          2 * ((n + 16) ^ 2 + 5 * (n + 16) + 4) := by
        simpa [Nat.add_assoc] using quadratic_step n
      _ ≤ 2 * 2 ^ (n + 18) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1 + 18) := by
        rw [show n + 1 + 18 = (n + 18) + 1 by omega]
        exact (Nat.mul_comm _ _).trans (pow_succ 2 (n + 18)).symm

theorem large_exponential_linear (v : ℕ) (hv : 16 ≤ v) :
    triangle v + 2 * v + 2 ≤ 2 ^ (v + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hv
  have hp := quadratic_le n
  have ha := triangle_twice (16 + n)
  have he : 2 ^ (n + 18) = 2 * 2 ^ (16 + n + 1) := by
    rw [show n + 18 = (16 + n + 1) + 1 by omega, pow_succ]
    omega
  rw [he] at hp
  nlinarith

theorem recurrence_le_budget (v u k N : ℕ) (hk : k ≤ v)
    (hzero : recurrenceBound v u 0 ≤ N)
    (hchanged : ∀ j < v, changedBound v u j ≤ N) :
    recurrenceBound v u k ≤ N + ∑ i ∈ Finset.range k, (exceptionalCount v u (i + 1) + 1) := by
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    have hd := ih (by omega)
    have he : (Finset.range (k + 1)).sup (changedBound v u) ≤ N := by
      apply Finset.sup_le
      intro j hj
      exact hchanged j (by have := Finset.mem_range.mp hj; omega)
    simp only [recurrenceBound, Finset.sum_range_succ]
    omega

theorem sum_descending (v : ℕ) : (∑ i ∈ Finset.range v, (v - i)) = triangle v := by
  have hr := Finset.sum_range_reflect (fun i : ℕ => i + 1) v
  have he : (∑ i ∈ Finset.range v, (v - 1 - i + 1)) =
      ∑ i ∈ Finset.range v, (v - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    omega
  rw [he] at hr
  rw [hr, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, mul_one]
  have hsum := Finset.sum_range_id_mul_two v
  have ha := triangle_twice v
  have hm : v * (v - 1) + 2 * v = v * (v + 1) := by
    cases v with
    | zero => simp
    | succ v => simp only [Nat.add_sub_cancel]; ring
  omega

theorem total_increment_le (v u : ℕ) :
    (∑ i ∈ Finset.range v, (exceptionalCount v u (i + 1) + 1)) ≤ triangle v * u + v := by
  have hb : ∀ i ∈ Finset.range v, exceptionalCount v u (i + 1) ≤ (v - i) * u := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold exceptionalCount
    split_ifs with h
    · have he : v - i = 1 := by omega
      simp [he]
    · have he : v - (i + 1) + 1 = v - i := by omega
      rw [he]
      exact Nat.mul_le_mul_left _ (oddDivisorCount_le u)
  calc
    _ ≤ ∑ i ∈ Finset.range v, ((v - i) * u + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.add_le_add_right (hb i hi) 1
    _ = triangle v * u + v := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_descending]
      simp

theorem large_gap (v u j : ℕ) (hv : 16 ≤ v) (hu : 1 ≤ u)
    (huv : u ≤ v) (hj : j < v) :
    triangle v * u + 2 * v + 1 ≤ (2 ^ v * u) / 2 ^ j + 2 ^ (j + 1) := by
  let m := 2 ^ v * u
  let C := triangle v + 2 * v + 1
  let B := triangle v * u + 2 * v + 1
  have hB : B ≤ u * C := by dsimp [B, C]; nlinarith
  have hsq : B ^ 2 ≤ 8 * m := by
    calc
      B ^ 2 ≤ (u * C) ^ 2 := Nat.pow_le_pow_left hB 2
      _ = (u * u) * C ^ 2 := by ring
      _ ≤ (u * v) * C ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left u huv)
      _ = u * (v * C ^ 2) := by ring
      _ ≤ u * 2 ^ (v + 3) := Nat.mul_le_mul_left u (large_exponential_square v hv)
      _ = 8 * m := by dsimp [m]; rw [pow_add]; norm_num; ring
  have hd : 2 ^ j ∣ m := dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) u
  have hm : (m / 2 ^ j) * 2 ^ j = m := Nat.div_mul_cancel hd
  have hprod : (m / 2 ^ j) * 2 ^ (j + 1) = 2 * m := by
    rw [pow_succ]
    nlinarith [hm]
  have ham := four_mul_le_sq_add (m / 2 ^ j) (2 ^ (j + 1))
  have hsq' : B ^ 2 ≤ (m / 2 ^ j + 2 ^ (j + 1)) ^ 2 := by nlinarith [hprod]
  change B ≤ m / 2 ^ j + 2 ^ (j + 1)
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (Nat.zero_le _) hsq'

theorem large_changedBound (v u j : ℕ) (hv : 16 ≤ v) (hu : 1 ≤ u)
    (huv : u ≤ v) (hj : j < v) :
    changedBound v u j + triangle v * u + v ≤ 2 * (2 ^ v * u) := by
  have hgap := large_gap v u j hv hu huv hj
  have hx : (2 ^ v * u) / 2 ^ j ≤ 2 ^ v * u := Nat.div_le_self _ _
  have hy : 2 ^ (j + 1) ≤ 2 ^ v * u := by
    calc
      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ 2 ^ v * u := Nat.le_mul_of_pos_right _ hu
  dsimp [changedBound]
  omega

theorem large_initial (v u : ℕ) (hv : 16 ≤ v) (hu : 1 ≤ u) :
    recurrenceBound v u 0 + triangle v * u + v ≤ 2 * (2 ^ v * u) := by
  have ht := oddDivisorCount_le u
  have he := Nat.mul_le_mul_left u (large_exponential_linear v hv)
  have he' : u * 2 ^ (v + 1) = 2 * (2 ^ v * u) := by rw [pow_succ]; ring
  rw [he'] at he
  have hd := Nat.mul_le_mul_left (v + 1) ht
  simp only [recurrenceBound]
  nlinarith

theorem large_bound (v u : ℕ) (hv : 16 ≤ v) (hu : 1 ≤ u)
    (huv : u ≤ v) : bound v u ≤ 2 * 2 ^ v * u := by
  let N := 2 * (2 ^ v * u) - (triangle v * u + v)
  have hi := large_initial v u hv hu
  have hzero : recurrenceBound v u 0 ≤ N := by dsimp [N]; omega
  have hc : ∀ j < v, changedBound v u j ≤ N := by
    intro j hj
    have h := large_changedBound v u j hv hu huv hj
    dsimp [N]
    omega
  have hr := recurrence_le_budget v u v N le_rfl hzero hc
  have ht := total_increment_le v u
  dsimp [N] at hr
  unfold bound
  have hm : 2 * (2 ^ v * u) = 2 * 2 ^ v * u := by ring
  rw [hm] at hr hi
  omega

end D5.S3.Combinatorics.Games.DivisorNimBoundArithmetic
