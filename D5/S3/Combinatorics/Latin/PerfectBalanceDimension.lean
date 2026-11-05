/- GID: D5/S3/Combinatorics/Latin/PerfectBalanceDimension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/PerfectBalanceDimension
   mirror-E: none(waiver:exact-finite-cut-energy-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Bernoulli]
   utility: none
   digest: A perfectly balanced Latin rectangle has at least half as many rows as columns. -/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Finite cut energies for the direct Latin-rectangle dimension bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Latin.PerfectBalanceDimension

open Finset

private def step (j x : ℕ) : ℚ := if j < x then 1 else 0

private theorem distance_cuts (n x y : ℕ) (hx : x ≤ n) (hy : y ≤ n) :
    |(x : ℚ) - y| = ∑ j ∈ range n, (step j x - step j y) ^ 2 := by
  have aux (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ n) :
      ∑ j ∈ range n, (step j x - step j y) ^ 2 = (y : ℚ) - x := by
    have he : (range n).filter (fun j => x ≤ j ∧ j < y) = Ico x y := by
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    calc
      _ = ∑ j ∈ range n, (if x ≤ j ∧ j < y then (1 : ℚ) else 0) := by
        apply sum_congr rfl
        intro j hj
        unfold step
        split_ifs <;> norm_num <;> omega
      _ = (y : ℚ) - x := by
        rw [sum_boole, he, Nat.card_Ico, Nat.cast_sub hxy]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (by exact sub_nonpos.mpr (by exact_mod_cast hxy)), aux x y hxy hy]
    ring
  · rw [abs_of_nonneg (by exact sub_nonneg.mpr (by exact_mod_cast hyx))]
    have h := aux y x hyx hx
    have he : (∑ j ∈ range n, (step j x - step j y) ^ 2) =
        ∑ j ∈ range n, (step j y - step j x) ^ 2 := by
      apply sum_congr rfl
      intro j hj
      ring
    rw [he, h]

private theorem cut_quadratic {α : Type} [Fintype α] (a b : α → ℚ)
    (ha : ∑ u, a u = 0) :
    -(∑ u, ∑ v, a u * a v * (b u - b v) ^ 2) = 2 * (∑ u, a u * b u) ^ 2 := by
  have hp (u v : α) : a u * a v * (b u - b v) ^ 2 =
      (a u * b u ^ 2) * a v + a u * (a v * b v ^ 2) -
        2 * (a u * b u) * (a v * b v) := by ring
  simp only [hp, sum_sub_distrib, sum_add_distrib, ← mul_sum, ha, mul_zero,
    zero_add, ← sum_mul]
  ring

private def energy {α : Type} [Fintype α] {n : ℕ} (a : α → ℚ)
    (p : α → Fin n) : ℚ :=
  -(∑ u, ∑ v, a u * a v * |((p u).val : ℚ) - (p v).val|)

private theorem energy_cuts {α : Type} [Fintype α] {n : ℕ} (a : α → ℚ)
    (p : α → Fin n) (ha : ∑ u, a u = 0) :
    energy a p = 2 * ∑ j ∈ range n, (∑ u, a u * step j (p u).val) ^ 2 := by
  unfold energy
  simp_rw [distance_cuts n _ _ (Nat.le_of_lt (p _).isLt) (Nat.le_of_lt (p _).isLt), mul_sum]
  simp_rw [sum_comm (s := univ) (t := range n)]
  rw [sum_neg_distrib, mul_sum]
  apply sum_congr rfl
  intro j hj
  exact cut_quadratic a (fun u => step j (p u).val) ha

private theorem energy_nonneg {α : Type} [Fintype α] {n : ℕ} (a : α → ℚ)
    (p : α → Fin n) (ha : ∑ u, a u = 0) : 0 ≤ energy a p := by
  rw [energy_cuts a p ha]
  positivity

private theorem power_sums (n : ℕ) :
    (∑ x ∈ range n, (x : ℚ)) = n * (n - 1) / 2 ∧
    (∑ x ∈ range n, (x : ℚ) ^ 2) = n * (n - 1) * (2 * n - 1) / 6 ∧
    (∑ x ∈ range n, (x : ℚ) ^ 3) = n ^ 2 * (n - 1) ^ 2 / 4 ∧
    (∑ x ∈ range n, (x : ℚ) ^ 4) =
      n * (n - 1) * (2 * n - 1) * (3 * n ^ 2 - 3 * n - 1) / 30 := by
  have h1 := sum_range_pow n 1
  have h2 := sum_range_pow n 2
  have h3 := sum_range_pow n 3
  have h4 := sum_range_pow n 4
  norm_num [sum_range_succ, bernoulli] at h1 h2 h3 h4
  exact ⟨by rw [h1]; ring, by rw [h2]; ring, by rw [h3]; ring, by rw [h4]; ring⟩

private def weight (n x : ℕ) : ℚ := 2 * x + 1 - n

private theorem weight_sum (n m : ℕ) :
    (∑ x ∈ range m, weight n x) = (m : ℚ) * (m - n) := by
  unfold weight
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul, mul_one]
  rw [(power_sums m).1]
  ring

private theorem weight_norm (n : ℕ) :
    (∑ x : Fin n, weight n x.val ^ 2) = (n : ℚ) * (n ^ 2 - 1) / 3 := by
  rw [Fin.sum_univ_eq_sum_range]
  have he (x : ℕ) : weight n x ^ 2 =
      4 * (x : ℚ) ^ 2 + (4 - 4 * n) * x + (1 - n) ^ 2 := by
    unfold weight
    ring
  simp_rw [he]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [(power_sums n).1, (power_sums n).2.1]
  ring

/-- A rectangular array with no repetition in any row or column. -/
structure LatinRectangle (k n : ℕ) where
  entry : Fin k → Fin n → Fin n
  row_injective : ∀ i, Function.Injective (entry i)
  column_injective : ∀ j, Function.Injective (fun i => entry i j)

/-- The column occupied by a symbol, as the inverse of its row permutation. -/
noncomputable def positions {k n : ℕ} (L : LatinRectangle k n) (i : Fin k) :
    Equiv.Perm (Fin n) :=
  (Equiv.ofBijective (L.entry i) (Finite.injective_iff_bijective.mp (L.row_injective i))).symm

/-- The sum of coordinate distances between two symbols. -/
def pairDistance {k n : ℕ} (L : LatinRectangle k n) (u v : Fin n) : ℚ :=
  ∑ i, |((positions L i u).val : ℚ) - (positions L i v).val|

/-- The sum of absolute deviations over unordered pairs of distinct symbols. -/
def imbalance {k n : ℕ} (L : LatinRectangle k n) : ℚ :=
  ∑ u, ∑ v, if u < v then |pairDistance L u v - (k : ℚ) * (n + 1) / 3| else 0

end D5.S3.Combinatorics.Latin.PerfectBalanceDimension
