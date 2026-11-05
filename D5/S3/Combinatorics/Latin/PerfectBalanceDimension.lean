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
  rw [← sum_neg_distrib]
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
  norm_num [sum_range_succ, bernoulli, Nat.choose] at h1 h2 h3 h4
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
  rw [Fin.sum_univ_eq_sum_range (fun x => weight n x ^ 2) n]
  have he (x : ℕ) : weight n x ^ 2 =
      4 * (x : ℚ) ^ 2 + (4 - 4 * n) * x + (1 - n) ^ 2 := by
    unfold weight
    ring
  simp_rw [he]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [(power_sums n).1, (power_sums n).2.1]
  ring

private theorem weight_zero (n : ℕ) (p : Equiv.Perm (Fin n)) :
    (∑ u, weight n (p u).val) = 0 := by
  rw [Equiv.sum_comp p (fun x : Fin n => weight n x.val),
    Fin.sum_univ_eq_sum_range (fun x => weight n x) n, weight_sum]
  ring

private theorem weight_tail (n : ℕ) (p : Equiv.Perm (Fin n)) (j : ℕ) (hj : j < n) :
    (∑ u, weight n (p u).val * step j (p u).val) =
      -((j : ℚ) + 1) * ((j : ℚ) + 1 - n) := by
  rw [Equiv.sum_comp p (fun x : Fin n => weight n x.val * step j x.val),
    Fin.sum_univ_eq_sum_range (fun x => weight n x * step j x) n]
  have hset : (range n).filter (fun x => x ≤ j) = range (j + 1) := by
    ext x
    simp only [mem_filter, mem_range]
    omega
  have hsplit : (∑ x ∈ range n, weight n x * step j x) =
      (∑ x ∈ range n, weight n x) - ∑ x ∈ range (j + 1), weight n x := by
    rw [← hset, sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x hx
    unfold step
    by_cases hjx : j < x
    · simp [hjx, show ¬ x ≤ j by omega]
    · simp [hjx, show x ≤ j by omega]
  rw [hsplit, weight_sum, weight_sum]
  push_cast
  ring

private theorem weight_energy (n : ℕ) (p : Equiv.Perm (Fin n)) :
    energy (fun u => weight n (p u).val) p = (n : ℚ) * (n ^ 4 - 1) / 15 := by
  rw [energy_cuts _ _ (weight_zero n p)]
  have hshift : (∑ j ∈ range n, (((j : ℚ) + 1) * ((j : ℚ) + 1 - n)) ^ 2) =
      ∑ j ∈ range n, ((j : ℚ) * ((j : ℚ) - n)) ^ 2 := by
    have h1 := sum_range_succ (fun j : ℕ => ((j : ℚ) * ((j : ℚ) - n)) ^ 2) n
    have h2 := sum_range_succ' (fun j : ℕ => ((j : ℚ) * ((j : ℚ) - n)) ^ 2) n
    norm_num at h1 h2
    linarith
  calc
    _ = 2 * ∑ j ∈ range n, (((j : ℚ) + 1) * ((j : ℚ) + 1 - n)) ^ 2 := by
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [weight_tail n p j (mem_range.mp hj)]
      ring
    _ = 2 * ∑ j ∈ range n, ((j : ℚ) * ((j : ℚ) - n)) ^ 2 := by rw [hshift]
    _ = 2 * ∑ j ∈ range n,
        ((j : ℚ) ^ 4 - 2 * n * (j : ℚ) ^ 3 + (n : ℚ) ^ 2 * (j : ℚ) ^ 2) := by
      congr 1
      apply sum_congr rfl
      intro j hj
      ring
    _ = (n : ℚ) * (n ^ 4 - 1) / 15 := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
      rw [(power_sums n).2.1, (power_sums n).2.2.1, (power_sums n).2.2.2]
      ring

/-- A rectangular array with no repetition in any row or column. -/
def LatinRectangle (k n : ℕ) :=
  {L : Fin k → Fin n → Fin n //
    (∀ i, Function.Injective (L i)) ∧ ∀ j, Function.Injective (fun i => L i j)}

/-- The column occupied by a symbol, as the inverse of its row permutation. -/
noncomputable def positions {k n : ℕ} (L : LatinRectangle k n) (i : Fin k) :
    Equiv.Perm (Fin n) :=
  (Equiv.ofBijective (L.val i) (Finite.injective_iff_bijective.mp (L.property.1 i))).symm

/-- The sum of coordinate distances between two symbols. -/
noncomputable def pairDistance {k n : ℕ} (L : LatinRectangle k n) (u v : Fin n) : ℚ :=
  ∑ i, |((positions L i u).val : ℚ) - (positions L i v).val|

/-- The sum of absolute deviations over unordered pairs of distinct symbols. -/
noncomputable def imbalance {k n : ℕ} (L : LatinRectangle k n) : ℚ :=
  ∑ u, ∑ v, if u < v then |pairDistance L u v - (k : ℚ) * (n + 1) / 3| else 0

private theorem balance_pairs {k n : ℕ} (L : LatinRectangle k n)
    (h : imbalance L = 0) (u v : Fin n) (huv : u ≠ v) :
    pairDistance L u v = (k : ℚ) * (n + 1) / 3 := by
  have hnonneg (u v : Fin n) :
      0 ≤ (if u < v then |pairDistance L u v - (k : ℚ) * (n + 1) / 3| else 0) := by
    split_ifs <;> positivity
  have hrow (u : Fin n) :
      (∑ v, if u < v then |pairDistance L u v - (k : ℚ) * (n + 1) / 3| else 0) = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun u _ => sum_nonneg (fun v _ => hnonneg u v))).mp h u (mem_univ u)
  have hpair (u v : Fin n) (h : u < v) :
      pairDistance L u v = (k : ℚ) * (n + 1) / 3 := by
    have hz := (sum_eq_zero_iff_of_nonneg (fun v _ => hnonneg u v)).mp (hrow u) v (mem_univ v)
    rw [ite_eq_left h] at hz
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hpair u v hlt
  · have hs : pairDistance L u v = pairDistance L v u := by
      unfold pairDistance
      apply sum_congr rfl
      intro i hi
      exact abs_sub_comm _ _
    exact hs.trans (hpair v u hgt)

private theorem total_energy {k n : ℕ} (L : LatinRectangle k n) (a : Fin n → ℚ)
    (ha : ∑ u, a u = 0) (h : imbalance L = 0) :
    (∑ i, energy a (positions L i)) =
      ((k : ℚ) * (n + 1) / 3) * ∑ u, a u ^ 2 := by
  let t : ℚ := (k : ℚ) * (n + 1) / 3
  have hp (u v : Fin n) : a u * a v * pairDistance L u v =
      (t * a u) * a v - if v = u then t * a u ^ 2 else 0 := by
    by_cases huv : u = v
    · subst v
      simp [pairDistance, pow_two, mul_assoc]
    · rw [balance_pairs L h u v huv, ite_eq_right (Ne.symm huv)]
      dsimp [t]
      ring
  have he : (∑ i, energy a (positions L i)) =
      -(∑ u, ∑ v, a u * a v * pairDistance L u v) := by
    simp only [energy, sum_neg_distrib]
    congr 1
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    rw [sum_comm]
    simp only [pairDistance, mul_sum]
  rw [he]
  simp only [hp, sum_sub_distrib, ← mul_sum, ha, mul_zero, sum_ite_eq', mem_univ,
    ite_true, zero_sub, sum_neg_distrib]
  dsimp [t]
  ring

/-- The full positive-size Latin-rectangle implication in Li--Ganesh, §10 Q5. -/
theorem result {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) (L : LatinRectangle k n)
    (h : imbalance L = 0) : n ≤ 2 * k := by
  by_cases hn : n = 1
  · omega
  have hn2 : 2 ≤ n := by omega
  let i : Fin k := ⟨0, hk⟩
  let p := positions L i
  let a : Fin n → ℚ := fun u => weight n (p u).val
  have ha : ∑ u, a u = 0 := weight_zero n p
  have hnorm : (∑ u, a u ^ 2) = (n : ℚ) * (n ^ 2 - 1) / 3 := by
    dsimp [a]
    rw [Equiv.sum_comp p (fun x : Fin n => weight n x.val ^ 2)]
    exact weight_norm n
  have henergy : energy a (positions L i) = (n : ℚ) * (n ^ 4 - 1) / 15 :=
    weight_energy n p
  have hbound : energy a (positions L i) ≤ ∑ j, energy a (positions L j) :=
    single_le_sum (fun j _ => energy_nonneg a (positions L j) ha) (mem_univ i)
  rw [henergy, total_energy L a ha h, hnorm] at hbound
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn2
  have hpositive : 0 < (n : ℚ) * (n ^ 2 - 1) := by nlinarith
  have hpoly : (n : ℚ) ^ 2 + 1 ≤ 5 * ((k : ℚ) * (n + 1) / 3) := by
    apply (mul_le_mul_iff_right₀ hpositive).mp
    nlinarith [hbound]
  have hlast : (n : ℚ) * 5 * (n + 1) ≤ 6 * (n ^ 2 + 1) := by
    have hcases : n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
    rcases hcases with rfl | rfl | hn4
    · norm_num
    · norm_num
    · have : (4 : ℚ) ≤ n := by exact_mod_cast hn4
      nlinarith [mul_nonneg (show (0 : ℚ) ≤ n - 2 by linarith)
        (show (0 : ℚ) ≤ n - 3 by linarith)]
  have hmul : (n : ℚ) * (n + 1) ≤ (2 * k) * (n + 1) := by nlinarith [hpoly, hlast]
  have hfin : (n : ℚ) ≤ 2 * k := (mul_le_mul_iff_left₀ (show (0 : ℚ) < n + 1 by positivity)).mp hmul
  exact_mod_cast hfin

end D5.S3.Combinatorics.Latin.PerfectBalanceDimension
