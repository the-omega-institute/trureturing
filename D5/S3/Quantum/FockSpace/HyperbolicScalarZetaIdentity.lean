/- GID: D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Eq. (C.12) of arXiv:2101.02399, a Bernoulli-harmonic-zeta identity, holds for all k. -/

/-
proof_shape: result: content
escape_witness: form (1): the private propositions `bh_eq` (Σ_i C(m,i) 2^i B_i = (2 - 2^m) B_m,
  from the exponential generating functions), `htail_eq` (Σ_j C(n-j,i)/j = C(n,i)(H_n - H_i))
  and `transB` (the harmonic-weighted binomial transform), on the live path of `result`
  through `transA`, `sum_R` and the telescoping in `rat_identity`
admission_basis: open-problem-resolution (issue #11322)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Harmonic.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.FockSpace.HyperbolicScalarZetaIdentity

open Finset Nat PowerSeries

/-- the weights `2^i B_i` -/
private def bw (i : ℕ) : ℚ := 2 ^ i * bernoulli i

/-- `bh m = Σ_i C(m,i) 2^i B_i` -/
private def bh (m : ℕ) : ℚ := ∑ i ∈ range (m + 1), (m.choose i : ℚ) * bw i

/-- `htail n i = Σ_{j=1}^{n} C(n - j, i) / j` -/
private def htail (n i : ℕ) : ℚ := ∑ j ∈ range n, ((n - (j + 1)).choose i : ℚ) / (j + 1)

private lemma htail_succ_succ (n i : ℕ) : htail (n + 1) (i + 1) = htail n (i + 1) + htail n i := by
  rw [htail, sum_range_succ, Nat.sub_self, Nat.choose_zero_succ, Nat.cast_zero, zero_div, add_zero,
    htail, htail, ← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  rw [show n + 1 - (j + 1) = (n - (j + 1)) + 1 by omega, Nat.choose_succ_succ, Nat.cast_add,
    add_div,
    add_comm]

private lemma htail_eq (n i : ℕ) : htail n i = (n.choose i : ℚ) * (harmonic n - harmonic i) := by
  induction n generalizing i with
  | zero => cases i <;> simp [htail]
  | succ n ih =>
    cases i with
    | zero =>
      rw [htail, harmonic]
      simp only [Nat.choose_zero_right, Nat.cast_one, harmonic_zero, sub_zero, one_mul]
      refine sum_congr rfl fun j _ => ?_
      push_cast; ring
    | succ i =>
      rw [htail_succ_succ, ih, ih, harmonic_succ n, harmonic_succ i, Nat.choose_succ_succ,
        Nat.cast_add]
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

private lemma bh_ext (m M : ℕ) (h : m ≤ M) :
    ∑ i ∈ range (M + 1), (m.choose i : ℚ) * bw i = bh m := by
  rw [bh]; symm
  apply sum_subset (range_subset_range.2 (by omega))
  intro i hi hni
  rw [Nat.choose_eq_zero_of_lt (by simp at hi hni; omega), Nat.cast_zero, zero_mul]

private lemma transA (n : ℕ) : ∑ i ∈ range (n + 1), (n.choose i : ℚ) * bw i * harmonic i =
    harmonic n * bh n - ∑ j ∈ range n, bh (n - (j + 1)) / (j + 1) := by
  have h1 : ∑ i ∈ range (n + 1), (n.choose i : ℚ) * bw i * (harmonic n - harmonic i) =
      ∑ j ∈ range n, bh (n - (j + 1)) / (j + 1) := by
    calc ∑ i ∈ range (n + 1), (n.choose i : ℚ) * bw i * (harmonic n - harmonic i)
        = ∑ i ∈ range (n + 1), ∑ j ∈ range n, ((n - (j + 1)).choose i : ℚ) * bw i / (j + 1) := by
          refine sum_congr rfl fun i _ => ?_
          rw [mul_right_comm, ← htail_eq, htail, sum_mul]
          refine sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ j ∈ range n, ∑ i ∈ range (n + 1), ((n - (j + 1)).choose i : ℚ) * bw i / (j + 1) :=
          sum_comm
      _ = ∑ j ∈ range n, bh (n - (j + 1)) / (j + 1) := by
          refine sum_congr rfl fun j _ => ?_
          rw [← sum_div, bh_ext _ _ (by omega)]
  rw [← h1, bh, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

private lemma transB (n : ℕ) : ∑ i ∈ range (n + 1), (n.choose i : ℚ) * bw i / i =
    ∑ j ∈ range (n + 1), (bh j - 1) / j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfirst : ∑ i ∈ range (n + 1), (n.choose i : ℚ) * bw (i + 1) / ((i + 1 : ℕ) : ℚ) =
        (bh (n + 1) - 1) / ((n + 1 : ℕ) : ℚ) := by
      have hb : bh (n + 1) =
          1 + ∑ i ∈ range (n + 1), ((n + 1).choose (i + 1) : ℚ) * bw (i + 1) := by
        rw [bh, sum_range_succ', add_comm]; simp [bw]
      rw [hb, add_sub_cancel_left, sum_div]
      refine sum_congr rfl fun i _ => ?_
      have h' : ((n + 1 : ℕ) : ℚ) * (n.choose i : ℚ) =
          ((n + 1).choose (i + 1) : ℚ) * ((i + 1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n i
      have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hi : ((i + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [div_eq_div_iff hi hn]
      linear_combination (bw (i + 1)) * h'
    have hsecond : ∑ i ∈ range (n + 1), (n.choose (i + 1) : ℚ) * bw (i + 1) / ((i + 1 : ℕ) : ℚ) =
        ∑ i ∈ range (n + 1), (n.choose i : ℚ) * bw i / i := by
      rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_div, add_zero,
        sum_range_succ' (fun i => (n.choose i : ℚ) * bw i / i)]
      simp
    rw [sum_range_succ (fun j => (bh j - 1) / (j : ℚ)) (n + 1), ← ih, ← hfirst, ← hsecond,
      sum_range_succ' (fun i => ((n + 1).choose i : ℚ) * bw i / i)]
    simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, add_div, sum_add_distrib,
      Nat.cast_zero, div_zero, add_zero, Nat.succ_eq_add_one]
    exact add_comm _ _

private lemma sum_range_two_mul (f : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ m ∈ range n, f (2 * m) + ∑ m ∈ range n, f (2 * m + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    ring

private lemma sum_Icc_one (g : ℕ → ℚ) (k : ℕ) : ∑ m ∈ Icc 1 k, g m = ∑ m ∈ range k, g (m + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [add_comm]

private lemma bh_eq (m : ℕ) : bh m = (2 - 2 ^ m) * bernoulli m := by
  have h : ∑ i ∈ range (m + 1), (m.choose i : ℚ) * (2 ^ i * bernoulli i) =
      (2 - 2 ^ m) * bernoulli m := by
    set E := bernoulliPowerSeries ℚ with hEdef
    set e : PowerSeries ℚ := exp ℚ with hedef
    have hE : E * (e - 1) = X := bernoulliPowerSeries_mul_exp_sub_one ℚ
    have he2 : rescale (2 : ℚ) e = e * e := by
      have h := exp_mul_exp_eq_exp_add (A := ℚ) 1 1
      rw [rescale_one, RingHom.id_apply] at h
      rw [h]; norm_num [hedef]
    have hE2 : rescale (2 : ℚ) E * (e * e - 1) = C (2 : ℚ) * X := by
      have h := congrArg (rescale (2 : ℚ)) hE
      rwa [map_mul, map_sub, map_one, he2, rescale_X] at h
    have hne : e * e - 1 ≠ 0 := by
      intro h
      have h1 := congrArg (coeff 1) h
      simp [hedef, coeff_mul, sum_antidiagonal_succ, coeff_exp] at h1
    have key : rescale (2 : ℚ) E * e = C (2 : ℚ) * E - rescale (2 : ℚ) E := by
      apply mul_right_cancel₀ hne
      have h3 : (C (2 : ℚ) * E - rescale (2 : ℚ) E) * (e * e - 1) =
          C (2 : ℚ) * (E * (e - 1)) * (e + 1) - rescale (2 : ℚ) E * (e * e - 1) := by ring
      rw [h3, hE, hE2]
      calc rescale (2 : ℚ) E * e * (e * e - 1) = rescale (2 : ℚ) E * (e * e - 1) * e := by ring
        _ = C (2 : ℚ) * X * e := by rw [hE2]
        _ = C (2 : ℚ) * X * (e + 1) - C (2 : ℚ) * X := by ring
    have hc := congrArg (coeff m) key
    rw [coeff_mul, map_sub, coeff_C_mul, coeff_rescale] at hc
    simp only [hEdef, hedef, bernoulliPowerSeries, coeff_rescale, coeff_mk, coeff_exp,
      Algebra.algebraMap_self, RingHom.id_apply] at hc
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
    have hf : ∀ n : ℕ, (n ! : ℚ) ≠ 0 := fun n => by exact_mod_cast factorial_ne_zero n
    have hterm : ∀ i ∈ range (m + 1),
        (2 : ℚ) ^ i * (bernoulli i / i !) * (1 / (m - i)! : ℚ) =
          ((m.choose i : ℚ) * (2 ^ i * bernoulli i)) / m ! := by
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
      have hch := Nat.choose_mul_factorial_mul_factorial hi'
      rw [eq_div_iff (hf m)]
      have hch' : ((m.choose i : ℚ) * i ! * (m - i)!) = m ! := by exact_mod_cast hch
      rw [← hch']
      field_simp
    rw [sum_congr rfl hterm, ← sum_div] at hc
    rw [div_eq_iff (hf m)] at hc
    rw [hc]
    field_simp
  rw [bh]; simpa [bw] using h

private lemma bh_odd (m : ℕ) : bh (2 * m + 1) = 0 := by
  rw [bh_eq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num
  · rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one m) (by omega), mul_zero]

private lemma bh_zero : bh 0 = 1 := by simp [bh, bw]

private lemma sum_inv_range (n : ℕ) : ∑ j ∈ range (n + 1), (1 : ℚ) / j = harmonic n := by
  rw [sum_range_succ', harmonic]; simp

private lemma sum_P (k : ℕ) : ∑ m ∈ Icc 1 k, bh (2 * m) / ((2 * m : ℕ) : ℚ) =
    ∑ i ∈ range (2 * k + 2 + 1), bh i / i - bh (2 * k + 2) / ((2 * k + 2 : ℕ) : ℚ) := by
  rw [sum_range_succ, add_sub_cancel_right, show 2 * k + 2 = 2 * (k + 1) by ring,
    sum_range_two_mul (fun i => bh i / (i : ℚ)) (k + 1)]
  simp only [bh_odd, zero_div, sum_const_zero, add_zero]
  rw [sum_range_succ', sum_Icc_one]
  simp

private lemma sum_Q (k : ℕ) :
    ∑ m ∈ Icc 1 k, bh (2 * m) / (((2 * k + 2 : ℕ) : ℚ) - ((2 * m : ℕ) : ℚ)) =
    ∑ j ∈ range (2 * k + 2), bh (2 * k + 2 - (j + 1)) / (j + 1) - 1 / ((2 * k + 2 : ℕ) : ℚ) := by
  have hrefl : ∑ j ∈ range (2 * k + 2), bh (2 * k + 2 - (j + 1)) / ((j : ℚ) + 1) =
      ∑ i ∈ range (2 * k + 2), bh i / (((2 * k + 2 : ℕ) : ℚ) - (i : ℚ)) := by
    rw [← sum_range_reflect (fun i => bh i / (((2 * k + 2 : ℕ) : ℚ) - (i : ℚ))) (2 * k + 2)]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    rw [show 2 * k + 2 - (j + 1) = 2 * k + 2 - 1 - j by omega]
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hrefl, show 2 * k + 2 = 2 * (k + 1) by ring,
    sum_range_two_mul (fun i => bh i / (((2 * (k + 1) : ℕ) : ℚ) - (i : ℚ))) (k + 1)]
  simp only [bh_odd, zero_div, sum_const_zero, add_zero]
  rw [sum_range_succ', sum_Icc_one, bh_zero]
  simp only [mul_zero, Nat.cast_zero, sub_zero, add_sub_cancel_right]

private lemma sum_R (n : ℕ) : ∑ j ∈ range n, (n.choose (j + 1) : ℚ) * bw (j + 1) * harmonic j =
    (harmonic n * bh n - ∑ j ∈ range n, bh (n - (j + 1)) / (j + 1)) -
      (∑ i ∈ range (n + 1), bh i / i - harmonic n) := by
  have hB : ∑ i ∈ range (n + 1), bh i / i - harmonic n =
      ∑ i ∈ range (n + 1), (n.choose i : ℚ) * bw i / i := by
    rw [transB, ← sum_inv_range, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [← transA, hB, sum_range_succ', sum_range_succ' (fun i => (n.choose i : ℚ) * bw i / i)]
  simp only [harmonic_zero, mul_zero, Nat.cast_zero, div_zero, add_zero, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [harmonic_succ]
  push_cast; ring

private theorem rat_identity (k : ℕ) :
    -((2 : ℚ) ^ (-(2 * k + 2 : ℤ)) / (k + 1)) * harmonic (2 * k + 1)
      - ∑ m ∈ Icc 1 k, (2 : ℚ) ^ (-(2 * k + 2 : ℤ)) * (2 ^ (2 * m) - 2) / ((k : ℚ) - m + 1) *
          (bernoulli (2 * m) / (2 * m))
      + ∑ j ∈ range (2 * k + 2), (-1) ^ j / (2 : ℚ) ^ ((2 * k : ℤ) - j) * ((2 * k + 1).choose j) *
          harmonic j * ((-1) ^ j * bernoulli (j + 1) / (j + 1))
      + (1 - (2 : ℚ) ^ (-(2 * k + 1 : ℤ))) * harmonic (2 * k + 1) *
          (bernoulli (2 * k + 2) / (k + 1)) = 0 := by
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
  -- the middle sum
  have hB : (2 : ℚ) ^ (2 * k + 2) * ((k : ℚ) + 1) * ∑ m ∈ Icc 1 k,
      ((2 : ℚ) ^ (2 * k + 2))⁻¹ * (2 ^ (2 * m) - 2) / ((k : ℚ) - m + 1) *
        (bernoulli (2 * m) / (2 * m)) =
      -(∑ m ∈ Icc 1 k, bh (2 * m) / ((2 * m : ℕ) : ℚ) +
        ∑ m ∈ Icc 1 k, bh (2 * m) / (((2 * k + 2 : ℕ) : ℚ) - ((2 * m : ℕ) : ℚ))) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmk⟩ := mem_Icc.mp hm
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hkm : (k : ℚ) - m + 1 ≠ 0 := by
      have : (m : ℚ) ≤ k := by exact_mod_cast hmk
      linarith
    have hkm2 : (2 * (k : ℚ) + 2) - 2 * m ≠ 0 := by
      have : (m : ℚ) ≤ k := by exact_mod_cast hmk
      linarith
    rw [bh_eq]
    push_cast
    rw [show (2 * (k : ℚ) + 2) - 2 * m = 2 * ((k : ℚ) - m + 1) by ring]
    field_simp
    ring
  -- the zeta sum
  have hC : (2 : ℚ) ^ (2 * k + 2) * ((k : ℚ) + 1) * ∑ j ∈ range (2 * k + 2),
      (-1) ^ j / (2 ^ (2 * k) / 2 ^ j) * ((2 * k + 1).choose j : ℚ) * harmonic j *
        ((-1) ^ j * bernoulli (j + 1) / (j + 1)) =
      ∑ j ∈ range (2 * k + 2), ((2 * k + 2).choose (j + 1) : ℚ) * bw (j + 1) * harmonic j := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have hch : ((2 * k + 2 : ℕ) : ℚ) * ((2 * k + 1).choose j : ℚ) =
        ((2 * k + 2).choose (j + 1) : ℚ) * ((j + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (2 * k + 1) j
    have hs : ((-1 : ℚ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
    have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
    rw [bw, div_div_eq_mul_div, show (-1 : ℚ) ^ j * 2 ^ j / 2 ^ (2 * k) *
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
  have hP := sum_P k
  have hQ := sum_Q k
  have hR := sum_R (2 * k + 2)
  have hbN := bh_eq (2 * k + 2)
  have hHN : harmonic (2 * k + 2) = harmonic (2 * k + 1) + 1 / ((2 * k + 2 : ℕ) : ℚ) := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, harmonic_succ, one_div]
  apply mul_left_cancel₀ hK
  rw [mul_zero]
  linear_combination hA - hB + hC + hD + hP + hQ + hR + (bh (2 * k + 2) + 1) * hHN +
    harmonic (2 * k + 1) * hbN

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
