/- GID: D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Eq. (C.12) of arXiv:2101.02399, a Bernoulli-harmonic-zeta identity, holds for all k. -/

/-
proof_shape: result: content
escape_witness: form (1): the private propositions `harmonic_choose`
  (Σ_{j=1}^{n} C(n-j,i)/j = C(n,i)(H_n - H_i), by induction) and `transB` (the transform of
  C(n,i) x_i / i, by induction), on the live path of `result` through `transA` and the
  telescoping in `rat_identity`; the value B_m(1/2) is Mathlib's `bernoulliFun_eval_half`
admission_basis: open-problem-resolution (issue #11322)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Harmonic.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.FockSpace.HyperbolicScalarZetaIdentity

open Finset Nat

/-- `Σ_{j=1}^{n} C(n - j, i) / j = C(n, i) (H_n - H_i)`. -/
private lemma harmonic_choose (n i : ℕ) :
    ∑ j ∈ range n, ((n - (j + 1)).choose i : ℚ) / (j + 1) =
      (n.choose i : ℚ) * (harmonic n - harmonic i) := by
  induction n generalizing i with
  | zero => cases i <;> simp
  | succ n ih =>
    cases i with
    | zero =>
      rw [harmonic]
      simp only [Nat.choose_zero_right, Nat.cast_one, harmonic_zero, sub_zero, one_mul]
      refine sum_congr rfl fun j _ => ?_
      push_cast; ring
    | succ i =>
      have hrec : ∑ j ∈ range (n + 1), ((n + 1 - (j + 1)).choose (i + 1) : ℚ) / (j + 1) =
          ∑ j ∈ range n, ((n - (j + 1)).choose (i + 1) : ℚ) / (j + 1) +
            ∑ j ∈ range n, ((n - (j + 1)).choose i : ℚ) / (j + 1) := by
        rw [sum_range_succ, Nat.sub_self, Nat.choose_zero_succ, Nat.cast_zero, zero_div, add_zero,
          ← sum_add_distrib]
        refine sum_congr rfl fun j hj => ?_
        have hj' := mem_range.mp hj
        rw [show n + 1 - (j + 1) = (n - (j + 1)) + 1 by omega, Nat.choose_succ_succ,
          Nat.cast_add, add_div, add_comm]
      rw [hrec, ih, ih, harmonic_succ n, harmonic_succ i, Nat.choose_succ_succ, Nat.cast_add]
      have hsm : ((n + 1 : ℕ) : ℚ) * (n.choose i : ℚ) =
          ((n.choose i : ℚ) + (n.choose (i + 1) : ℚ)) * (i + 1 : ℕ) := by
        have h := Nat.add_one_mul_choose_eq n i
        rw [Nat.choose_succ_succ] at h
        exact_mod_cast h
      have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hi : ((i + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have key : ((n.choose i : ℚ) + (n.choose (i + 1) : ℚ)) * ((n + 1 : ℕ) : ℚ)⁻¹ =
          (n.choose i : ℚ) * ((i + 1 : ℕ) : ℚ)⁻¹ := by
        field_simp
        linarith [hsm]
      simp only [Nat.succ_eq_add_one] at *
      push_cast at key ⊢
      linear_combination (-1 : ℚ) * key

/-- For any sequence `x` with binomial transform `y m = Σ_i C(m, i) x i`:
`Σ_i C(n, i) x i H_i = H_n y n - Σ_{j=1}^{n} y (n - j) / j`. -/
private lemma transA (x : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℚ) * x i * harmonic i =
      harmonic n * ∑ i ∈ range (n + 1), (n.choose i : ℚ) * x i -
        ∑ j ∈ range n, (∑ i ∈ range (n + 1), ((n - (j + 1)).choose i : ℚ) * x i) / (j + 1) := by
  have h1 : ∑ i ∈ range (n + 1), (n.choose i : ℚ) * x i * (harmonic n - harmonic i) =
      ∑ j ∈ range n, (∑ i ∈ range (n + 1), ((n - (j + 1)).choose i : ℚ) * x i) / (j + 1) := by
    calc ∑ i ∈ range (n + 1), (n.choose i : ℚ) * x i * (harmonic n - harmonic i)
        = ∑ i ∈ range (n + 1), ∑ j ∈ range n, ((n - (j + 1)).choose i : ℚ) * x i / (j + 1) := by
          refine sum_congr rfl fun i _ => ?_
          rw [mul_right_comm, ← harmonic_choose, sum_mul]
          refine sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ j ∈ range n, ∑ i ∈ range (n + 1), ((n - (j + 1)).choose i : ℚ) * x i / (j + 1) :=
          sum_comm
      _ = _ := by
          refine sum_congr rfl fun j _ => ?_
          rw [sum_div]
  rw [← h1, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- For any sequence `x`: `Σ_i C(n, i) x i / i = Σ_{j=1}^{n} (y j - x 0) / j`, where
`y j = Σ_i C(j, i) x i`. -/
private lemma transB (x : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℚ) * x i / i =
      ∑ j ∈ range (n + 1), (∑ i ∈ range (j + 1), (j.choose i : ℚ) * x i - x 0) / j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfirst : ∑ i ∈ range (n + 1), (n.choose i : ℚ) * x (i + 1) / ((i + 1 : ℕ) : ℚ) =
        (∑ i ∈ range (n + 1 + 1), ((n + 1).choose i : ℚ) * x i - x 0) / ((n + 1 : ℕ) : ℚ) := by
      rw [sum_range_succ' (fun i => ((n + 1).choose i : ℚ) * x i) (n + 1), Nat.choose_zero_right,
        Nat.cast_one, one_mul, add_sub_cancel_right, sum_div]
      refine sum_congr rfl fun i _ => ?_
      have h' : ((n + 1 : ℕ) : ℚ) * (n.choose i : ℚ) =
          ((n + 1).choose (i + 1) : ℚ) * ((i + 1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n i
      have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hi : ((i + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [div_eq_div_iff hi hn]
      linear_combination (x (i + 1)) * h'
    have hsecond : ∑ i ∈ range (n + 1), (n.choose (i + 1) : ℚ) * x (i + 1) / ((i + 1 : ℕ) : ℚ) =
        ∑ i ∈ range (n + 1), (n.choose i : ℚ) * x i / i := by
      rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_div, add_zero,
        sum_range_succ' (fun i => (n.choose i : ℚ) * x i / i)]
      simp
    rw [sum_range_succ (fun j => (∑ i ∈ range (j + 1), (j.choose i : ℚ) * x i - x 0) / (j : ℚ))
      (n + 1), ← ih, ← hfirst, ← hsecond,
      sum_range_succ' (fun i => ((n + 1).choose i : ℚ) * x i / i)]
    simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, add_div, sum_add_distrib,
      Nat.cast_zero, div_zero, add_zero, Nat.succ_eq_add_one]
    exact add_comm _ _

private theorem rat_identity (k : ℕ) :
    -((2 : ℚ) ^ (-(2 * k + 2 : ℤ)) / (k + 1)) * harmonic (2 * k + 1)
      - ∑ m ∈ Icc 1 k, (2 : ℚ) ^ (-(2 * k + 2 : ℤ)) * (2 ^ (2 * m) - 2) / ((k : ℚ) - m + 1) *
          (bernoulli (2 * m) / (2 * m))
      + ∑ j ∈ range (2 * k + 2), (-1) ^ j / (2 : ℚ) ^ ((2 * k : ℤ) - j) * ((2 * k + 1).choose j) *
          harmonic j * ((-1) ^ j * bernoulli (j + 1) / (j + 1))
      + (1 - (2 : ℚ) ^ (-(2 * k + 1 : ℤ))) * harmonic (2 * k + 1) *
          (bernoulli (2 * k + 2) / (k + 1)) = 0 := by
  -- the weights `x i = 2^i B_i` and their binomial transform `y m = 2^m B_m(1/2)`
  set x : ℕ → ℚ := fun i => 2 ^ i * bernoulli i with hx
  set y : ℕ → ℚ := fun m => ∑ i ∈ range (m + 1), (m.choose i : ℚ) * x i with hy
  have hyval : ∀ m, y m = (2 - 2 ^ m) * bernoulli m := by
    intro m
    have h := bernoulliFun_eval_half m
    simp only [bernoulliFun, Polynomial.bernoulli, Polynomial.eval_map, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_monomial] at h
    have h2 : ((y m : ℚ) : ℝ) = (2 : ℝ) ^ m * ∑ i ∈ range (m + 1),
        algebraMap ℚ ℝ (bernoulli i * m.choose i) * 2⁻¹ ^ (m - i) := by
      simp only [hy, hx]
      push_cast
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [← pow_mul_pow_sub (2 : ℝ) hi', inv_pow]
      field_simp
      simp only [eq_ratCast]
    rw [h] at h2
    have h3 : ((y m : ℚ) : ℝ) = (((2 - 2 ^ m) * bernoulli m : ℚ) : ℝ) := by
      rw [h2]; push_cast; field_simp
    exact_mod_cast h3
  have hx0 : x 0 = 1 := by simp [hx]
  have hy0 : y 0 = 1 := by simp [hy, hx]
  have hodd : ∀ m, y (2 * m + 1) = 0 := by
    intro m
    rw [hyval]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num
    · rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one m) (by omega), mul_zero]
  have hext : ∀ m M, m ≤ M → ∑ i ∈ range (M + 1), (m.choose i : ℚ) * x i = y m := by
    intro m M hmM
    simp only [hy]; symm
    apply sum_subset (range_subset_range.2 (by omega))
    intro i hi hni
    rw [Nat.choose_eq_zero_of_lt (by simp at hi hni; omega), Nat.cast_zero, zero_mul]
  have hsplit : ∀ (f : ℕ → ℚ) (n : ℕ),
      ∑ i ∈ range (2 * n), f i = ∑ m ∈ range n, f (2 * m) + ∑ m ∈ range n, f (2 * m + 1) := by
    intro f n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
        sum_range_succ, sum_range_succ]
      ring
  have hIcc : ∀ g : ℕ → ℚ, ∑ m ∈ range (k + 1), g m = g 0 + ∑ m ∈ Icc 1 k, g m := by
    intro g
    rw [sum_range_succ', add_comm, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp [add_comm]
  -- the halves of the middle sum
  have hP : ∑ m ∈ Icc 1 k, y (2 * m) / ((2 * m : ℕ) : ℚ) =
      ∑ i ∈ range (2 * k + 2 + 1), y i / i - y (2 * k + 2) / ((2 * k + 2 : ℕ) : ℚ) := by
    rw [sum_range_succ, add_sub_cancel_right, show 2 * k + 2 = 2 * (k + 1) by ring,
      hsplit (fun i => y i / (i : ℚ)) (k + 1), hIcc]
    simp [hodd]
  have hQ : ∑ m ∈ Icc 1 k, y (2 * m) / (((2 * k + 2 : ℕ) : ℚ) - ((2 * m : ℕ) : ℚ)) =
      ∑ j ∈ range (2 * k + 2), y (2 * k + 2 - (j + 1)) / (j + 1) - 1 / ((2 * k + 2 : ℕ) : ℚ) := by
    have hrefl : ∑ j ∈ range (2 * k + 2), y (2 * k + 2 - (j + 1)) / ((j : ℚ) + 1) =
        ∑ i ∈ range (2 * k + 2), y i / (((2 * k + 2 : ℕ) : ℚ) - (i : ℚ)) := by
      rw [← sum_range_reflect (fun i => y i / (((2 * k + 2 : ℕ) : ℚ) - (i : ℚ))) (2 * k + 2)]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [show 2 * k + 2 - (j + 1) = 2 * k + 2 - 1 - j by omega]
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    rw [hrefl, show 2 * k + 2 = 2 * (k + 1) by ring,
      hsplit (fun i => y i / (((2 * (k + 1) : ℕ) : ℚ) - (i : ℚ))) (k + 1), hIcc]
    simp only [hodd, zero_div, sum_const_zero, add_zero, hy0, mul_zero, Nat.cast_zero, sub_zero]
    ring
  -- the zeta sum through the two transforms
  have hR : ∑ j ∈ range (2 * k + 2), ((2 * k + 2).choose (j + 1) : ℚ) * x (j + 1) * harmonic j =
      (harmonic (2 * k + 2) * y (2 * k + 2) -
        ∑ j ∈ range (2 * k + 2), y (2 * k + 2 - (j + 1)) / (j + 1)) -
      (∑ i ∈ range (2 * k + 2 + 1), y i / i - harmonic (2 * k + 2)) := by
    have hA := transA x (2 * k + 2)
    have hB := transB x (2 * k + 2)
    rw [hext _ _ le_rfl] at hA
    have hA' : ∑ j ∈ range (2 * k + 2),
        (∑ i ∈ range (2 * k + 2 + 1), ((2 * k + 2 - (j + 1)).choose i : ℚ) * x i) / (j + 1) =
        ∑ j ∈ range (2 * k + 2), y (2 * k + 2 - (j + 1)) / (j + 1) :=
      sum_congr rfl fun j _ => by rw [hext _ _ (by omega)]
    rw [hA'] at hA
    have hH : ∑ j ∈ range (2 * k + 2 + 1), (1 : ℚ) / j = harmonic (2 * k + 2) := by
      rw [sum_range_succ', harmonic]; simp
    have hB' : ∑ i ∈ range (2 * k + 2 + 1), y i / i - harmonic (2 * k + 2) =
        ∑ i ∈ range (2 * k + 2 + 1), ((2 * k + 2).choose i : ℚ) * x i / i := by
      rw [hB, ← hH, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [hx0]; simp only [hy]; ring
    rw [← hA, hB', sum_range_succ' (fun i => ((2 * k + 2).choose i : ℚ) * x i * harmonic i),
      sum_range_succ' (fun i => ((2 * k + 2).choose i : ℚ) * x i / i)]
    simp only [harmonic_zero, mul_zero, Nat.cast_zero, div_zero, add_zero, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [harmonic_succ]
    push_cast; ring
  -- the powers of two
  have hz1 : (2 : ℚ) ^ (-(2 * k + 2 : ℤ)) = ((2 : ℚ) ^ (2 * k + 2))⁻¹ := by
    rw [show (-(2 * k + 2 : ℤ)) = -((2 * k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hz2 : (2 : ℚ) ^ (-(2 * k + 1 : ℤ)) = ((2 : ℚ) ^ (2 * k + 1))⁻¹ := by
    rw [show (-(2 * k + 1 : ℤ)) = -((2 * k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hz3 : ∀ j : ℕ, (2 : ℚ) ^ ((2 * k : ℤ) - j) = 2 ^ (2 * k) / 2 ^ j := by
    intro j
    rw [zpow_sub₀ two_ne_zero, show ((2 * k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, zpow_natCast]
  rw [hz1, hz2]
  simp only [hz3]
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ (2 * k + 2) ≠ 0 := by positivity
  have hK : (2 : ℚ) ^ (2 * k + 2) * ((k : ℚ) + 1) ≠ 0 := mul_ne_zero h2 hk1
  -- each part times `2^(2k+2) (k+1)`
  have hM : (2 : ℚ) ^ (2 * k + 2) * ((k : ℚ) + 1) * ∑ m ∈ Icc 1 k,
      ((2 : ℚ) ^ (2 * k + 2))⁻¹ * (2 ^ (2 * m) - 2) / ((k : ℚ) - m + 1) *
        (bernoulli (2 * m) / (2 * m)) =
      -(∑ m ∈ Icc 1 k, y (2 * m) / ((2 * m : ℕ) : ℚ) +
        ∑ m ∈ Icc 1 k, y (2 * m) / (((2 * k + 2 : ℕ) : ℚ) - ((2 * m : ℕ) : ℚ))) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmk⟩ := mem_Icc.mp hm
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hkm : (k : ℚ) - m + 1 ≠ 0 := by
      have : (m : ℚ) ≤ k := by exact_mod_cast hmk
      linarith
    rw [hyval]
    push_cast
    rw [show (2 * (k : ℚ) + 2) - 2 * m = 2 * ((k : ℚ) - m + 1) by ring]
    field_simp
    ring
  have hC : (2 : ℚ) ^ (2 * k + 2) * ((k : ℚ) + 1) * ∑ j ∈ range (2 * k + 2),
      (-1) ^ j / (2 ^ (2 * k) / 2 ^ j) * ((2 * k + 1).choose j : ℚ) * harmonic j *
        ((-1) ^ j * bernoulli (j + 1) / (j + 1)) =
      ∑ j ∈ range (2 * k + 2), ((2 * k + 2).choose (j + 1) : ℚ) * x (j + 1) * harmonic j := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have hch : ((2 * k + 2 : ℕ) : ℚ) * ((2 * k + 1).choose j : ℚ) =
        ((2 * k + 2).choose (j + 1) : ℚ) * ((j + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (2 * k + 1) j
    have hs : ((-1 : ℚ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
    have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
    simp only [hx]
    rw [div_div_eq_mul_div, show (-1 : ℚ) ^ j * 2 ^ j / 2 ^ (2 * k) *
        ((2 * k + 1).choose j : ℚ) * harmonic j * ((-1) ^ j * bernoulli (j + 1) / (j + 1)) =
        ((-1) ^ j * (-1) ^ j) * 2 ^ j / 2 ^ (2 * k) *
        ((2 * k + 1).choose j : ℚ) * harmonic j * bernoulli (j + 1) / (j + 1) by ring, hs,
      show (2 : ℚ) ^ (2 * k + 2) = 2 ^ (2 * k) * 4 by rw [pow_add]; norm_num]
    have h2k : (2 : ℚ) ^ (2 * k) ≠ 0 := by positivity
    push_cast at hch ⊢
    field_simp
    linear_combination (2 * 2 ^ j * harmonic j * bernoulli (j + 1)) * hch
  have hA : (2 : ℚ) ^ (2 * k + 2) * ((k : ℚ) + 1) *
      (-(((2 : ℚ) ^ (2 * k + 2))⁻¹ / (k + 1)) * harmonic (2 * k + 1)) = -harmonic (2 * k + 1) := by
    field_simp
  have hD : (2 : ℚ) ^ (2 * k + 2) * ((k : ℚ) + 1) * ((1 - ((2 : ℚ) ^ (2 * k + 1))⁻¹) *
      harmonic (2 * k + 1) * (bernoulli (2 * k + 2) / (k + 1))) =
      (2 ^ (2 * k + 2) - 2) * harmonic (2 * k + 1) * bernoulli (2 * k + 2) := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ]
    field_simp
  have hyN := hyval (2 * k + 2)
  have hHN : harmonic (2 * k + 2) = harmonic (2 * k + 1) + 1 / ((2 * k + 2 : ℕ) : ℚ) := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, harmonic_succ, one_div]
  apply mul_left_cancel₀ hK
  rw [mul_zero]
  linear_combination hA - hM + hC + hD + hP + hQ + hR + (y (2 * k + 2) + 1) * hHN +
    harmonic (2 * k + 1) * hyN

/-- Eq. (C.12) of arXiv:2101.02399 (`conjecture1` of the arXiv source), for every `k`. -/
def claim : Prop :=
  ∀ k : ℕ,
    -((2 : ℂ) ^ (-(2 * k + 2 : ℤ)) / (k + 1)) * harmonic (2 * k + 1)
      - ∑ m ∈ Icc 1 k, (2 : ℂ) ^ (-(2 * k + 2 : ℤ)) * (2 ^ (2 * m) - 2) / ((k : ℂ) - m + 1) *
          (bernoulli (2 * m) / (2 * m))
      + ∑ j ∈ range (2 * k + 2), (-1) ^ j / (2 : ℂ) ^ ((2 * k : ℤ) - j) *
          ((2 * k + 1).choose j) * harmonic j * riemannZeta (-j)
      + (1 - (2 : ℂ) ^ (-(2 * k + 1 : ℤ))) * harmonic (2 * k + 1) *
          (bernoulli (2 * k + 2) / (k + 1)) = 0

/-- The identity holds for every `k`. -/
theorem result : claim := by
  intro k
  simp only [riemannZeta_neg_nat_eq_bernoulli]
  have h := congrArg (fun x : ℚ => (x : ℂ)) (rat_identity k)
  push_cast at h
  exact h

end D5.S3.Quantum.FockSpace.HyperbolicScalarZetaIdentity
