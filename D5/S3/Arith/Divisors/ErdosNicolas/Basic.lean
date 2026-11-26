/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Basic
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/ErdosNicolas/Basic
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Reciprocal divisor gaps, dilation identities, and prime power bounds. -/

import Mathlib.Data.Nat.Dist
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! General rational interfaces for reciprocal divisor gaps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- Sum of reciprocal positive gaps, counting each unordered pair once. -/
def pairSum (S : Finset ℕ) : ℚ :=
  ∑ d ∈ S, ∑ e ∈ S, if d < e then ((e - d : ℕ) : ℚ)⁻¹ else 0

/-- The unnormalized Erdős–Nicolas reciprocal divisor gap sum. -/
def hHat (n : ℕ) : ℚ := pairSum n.divisors

/-- The exceptional integers in the strengthened induction statement. -/
def exceptions : Finset ℕ :=
  {12, 24, 60, 120, 180, 240, 360, 420, 720, 840, 1260, 1680, 2520, 5040}

/-- Strong induction target, including both strict exceptional inequalities. -/
def Good (n : ℕ) : Prop :=
  if n ∈ exceptions then
    (n.divisors.card : ℚ) < hHat n ∧ 7 * hHat n < 8 * (n.divisors.card : ℚ)
  else hHat n < (n.divisors.card : ℚ)

/-- The Erdős–Nicolas conjecture above its last exceptional integer. -/
def ErdosNicolasClaim : Prop :=
  ∀ n : ℕ, 5040 < n → hHat n < (n.divisors.card : ℚ)

/-- Dilating the points by `p` divides the reciprocal gap sum by `p`. -/
theorem pairSum_mul_image (p : ℕ) (S : Finset ℕ) :
    pairSum (S.image (p * ·)) = pairSum S / (p : ℚ) := by
  by_cases hp0 : p = 0
  · subst p
    simp only [pairSum, zero_mul, Nat.cast_zero, div_zero]
    apply sum_eq_zero
    intro x hx
    obtain ⟨d, _, rfl⟩ := mem_image.mp hx
    apply sum_eq_zero
    intro y hy
    obtain ⟨e, _, rfl⟩ := mem_image.mp hy
    simp
  have hp : 0 < p := Nat.pos_of_ne_zero hp0
  have hinj : Function.Injective (p * ·) := by
    intro x y h
    exact Nat.eq_of_mul_eq_mul_left hp h
  unfold pairSum
  simp only [sum_image hinj.injOn]
  simp_rw [Nat.mul_lt_mul_left hp, ← Nat.mul_sub_left_distrib, Nat.cast_mul,
    mul_inv_rev]
  rw [div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro d _
  rw [sum_mul]
  apply sum_congr rfl
  intro e _
  split_ifs <;> simp [mul_comm]

/-- The inverse-distance matrix has zero diagonal and counts both orientations. -/
theorem sum_inv_dist (S : Finset ℕ) :
    (∑ d ∈ S, ∑ e ∈ S, ((Nat.dist d e : ℕ) : ℚ)⁻¹) = 2 * pairSum S := by
  have hpoint (d e : ℕ) : ((Nat.dist d e : ℕ) : ℚ)⁻¹ =
      (if d < e then ((e - d : ℕ) : ℚ)⁻¹ else 0) +
      (if e < d then ((d - e : ℕ) : ℚ)⁻¹ else 0) := by
    rcases lt_trichotomy d e with h | rfl | h
    · simp [h, Nat.not_lt.mpr h.le, Nat.dist_eq_sub_of_le h.le]
    · simp [Nat.dist_self]
    · simp [h, Nat.not_lt.mpr h.le, Nat.dist_eq_sub_of_le_right h.le]
  simp_rw [hpoint, sum_add_distrib]
  have hswap : (∑ d ∈ S, ∑ e ∈ S,
      if e < d then ((d - e : ℕ) : ℚ)⁻¹ else 0) = pairSum S := by
    rw [sum_comm]
    rfl
  change pairSum S + _ = _
  rw [hswap]
  ring

private theorem exponent_le_pow {p : ℕ} (hp : 2 ≤ p) (k : ℕ) : k + 1 ≤ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hpos : 1 ≤ p ^ k := Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ (by omega : p ≠ 0))
    nlinarith

private theorem prime_row_bound {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∑ i ∈ range (k + 1), ((p ^ (k + 1) - p ^ i : ℕ) : ℚ)⁻¹) ≤ 1 := by
  have hpow : 0 < p ^ k := pow_pos hp.pos _
  have hgap (i : ℕ) (hi : i ∈ range (k + 1)) :
      p ^ k ≤ p ^ (k + 1) - p ^ i := by
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hpi := Nat.pow_le_pow_right hp.pos hi'
    have hp2 := hp.two_le
    have hmul : p ^ k + p ^ i ≤ p ^ (k + 1) := by
      rw [pow_succ]
      nlinarith
    omega
  calc
    _ ≤ ∑ _i ∈ range (k + 1), ((p ^ k : ℕ) : ℚ)⁻¹ := by
      apply sum_le_sum
      intro i hi
      exact inv_anti₀ (by exact_mod_cast hpow) (by exact_mod_cast hgap i hi)
    _ = ((k + 1 : ℕ) : ℚ) / ((p ^ k : ℕ) : ℚ) := by simp [div_eq_mul_inv]
    _ ≤ 1 := by
      apply (div_le_one (by exact_mod_cast hpow)).mpr
      exact_mod_cast exponent_le_pow hp.two_le k

/-- Every positive-exponent row contributes at most one; the zeroth row is empty. -/
theorem hHat_prime_pow_le {p : ℕ} (hp : p.Prime) (a : ℕ) : hHat (p ^ a) ≤ a := by
  unfold hHat pairSum
  simp only [Nat.sum_divisors_prime_pow hp]
  rw [sum_comm]
  have hrow (j : ℕ) (hj : j ∈ range (a + 1)) :
      (∑ i ∈ range (a + 1),
        if p ^ i < p ^ j then ((p ^ j - p ^ i : ℕ) : ℚ)⁻¹ else 0) =
      ∑ i ∈ range j, ((p ^ j - p ^ i : ℕ) : ℚ)⁻¹ := by
    calc
      _ = ∑ i ∈ range j,
          if p ^ i < p ^ j then ((p ^ j - p ^ i : ℕ) : ℚ)⁻¹ else 0 := by
        symm
        apply sum_subset (range_mono (Nat.le_of_lt (mem_range.mp hj)))
        intro i _ hi
        have hij : ¬ i < j := by simpa only [mem_range] using hi
        simp only [Nat.pow_lt_pow_iff_right hp.one_lt, hij, ↓reduceIte]
      _ = _ := by
        apply sum_congr rfl
        intro i hi
        have hij : i < j := mem_range.mp hi
        simp only [(Nat.pow_lt_pow_iff_right hp.one_lt).mpr hij, ↓reduceIte]
  rw [show (∑ j ∈ range (a + 1), ∑ i ∈ range (a + 1),
      if p ^ i < p ^ j then ((p ^ j - p ^ i : ℕ) : ℚ)⁻¹ else 0) =
      ∑ j ∈ range (a + 1), ∑ i ∈ range j,
        ((p ^ j - p ^ i : ℕ) : ℚ)⁻¹ from sum_congr rfl hrow]
  clear hrow
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ]
    have h := prime_row_bound hp a
    rw [Nat.cast_add, Nat.cast_one]
    linarith

#print axioms pairSum_mul_image
#print axioms sum_inv_dist
#print axioms hHat_prime_pow_le

end D5.S3.Arith.ErdosNicolas
