/- GID: D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo
   generality: I
   mirror-B: D5/B/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna bilateral coefficients at powers of two. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19885
admission_basis: open-problem-resolution (#18659; Proved)
escape_witness: none
Direct frozen dependencies: none.
utility: none; all results are universal identities, with no finite enumeration.
The literal source coefficient expression is retained over complex formal power series.
posTerm, negTerm, posVal and negVal are private coefficient-calculation definitions.
coeff_C_add_X_pow: proof_shape: bind-only; escape_witness: none; consumers: coeff_pos_mul.
inverse_linear_pow: proof_shape: bind-only; escape_witness: none; consumers: coeff_inverse_linear_pow.
coeff_inverse_linear_pow: proof_shape: bind-only; escape_witness: none; consumers: coeff_neg_mul.
posTerm_expand: proof_shape: bind-only; escape_witness: none; consumers: coeff_pos_mul, coeff_pos_not_dvd.
inverse_linear_expand: proof_shape: bind-only; escape_witness: none; consumers: negTerm_expand.
negTerm_expand: proof_shape: bind-only; escape_witness: none; consumers: coeff_neg_mul, coeff_neg_not_dvd.
coeff_pos_mul: proof_shape: bind-only; escape_witness: none; consumers: coeffA_divisors.
coeff_neg_mul: proof_shape: bind-only; escape_witness: none; consumers: coeffA_divisors.
coeff_pos_not_dvd: proof_shape: bind-only; escape_witness: none; consumers: coeffA_divisors.
coeff_neg_not_dvd: proof_shape: bind-only; escape_witness: none; consumers: coeffA_divisors.
coeffA_divisors: proof_shape: bind-only; escape_witness: none; consumers: coeffA_prime, coeffA_pow_two.
coeffA_prime: proof_shape: bind-only; escape_witness: none; consumers: OeisA363558Prime.result, OeisA363559Prime.result, OeisA363561Prime.result, OeisA363569Prime.result.
vals_pair: proof_shape: bind-only; escape_witness: none; consumers: coeffA_pow_two.
dyadic_quotients: proof_shape: bind-only; escape_witness: none; consumers: coeffA_pow_two.
coeffA_pow_two: proof_shape: bind-only; escape_witness: none; consumers: result, OeisA363559PowerOfTwo.result, OeisA363561PowerOfTwo.result, OeisA363569PowerOfTwo.result.
result: proof_shape: bind-only; escape_witness: none; settling result.
-/

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

namespace D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo

open PowerSeries

/-- The coefficient of `x^m` in `∑_{n ∈ ℤ} x^n (c + x^n)^(2n)`. A term with `n ≥ 0` is a polynomial; a term with
`n = -k`, `k ≥ 1`, equals `x^(2k² - k) (1 + c x^k)^(-2k)`. Only `n ≤ m` and `k ≤ m` contribute to `x^m`. -/
noncomputable def coeffA (c : ℂ) (m : ℕ) : ℂ :=
  (∑ n ∈ Finset.range (m + 1), coeff m ((X : ℂ⟦X⟧) ^ n * (C c + X ^ n) ^ (2 * n))) +
    ∑ k ∈ Finset.Icc 1 m, coeff m ((X : ℂ⟦X⟧) ^ (2 * k ^ 2 - k) * ((1 + C c * X ^ k) ^ (2 * k))⁻¹)

/-- A363558: the coefficients for `c = 2`. -/
noncomputable def a (m : ℕ) : ℂ := coeffA 2 m

/-- A363558 ("a(2^n) = 4^(2^n) for n > 0 (conjecture)"). -/
def claim : Prop := ∀ n : ℕ, 0 < n → a (2 ^ n) = 4 ^ (2 ^ n)

end D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo


namespace D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
open PowerSeries

private lemma coeff_C_add_X_pow (c : ℂ) (d j : ℕ) :
    coeff j ((C c + X : ℂ⟦X⟧)^d) = c^(d-j) * (d.choose j : ℂ) := by
  have h := Polynomial.coeff_X_add_C_pow c d j
  rw [← Polynomial.coeff_coe] at h
  simpa only [Polynomial.coeff_coe, Polynomial.coe_pow, Polynomial.coe_add,
    Polynomial.coe_X, Polynomial.coe_C, add_comm] using h

private lemma inverse_linear_pow (c : ℂ) (d : ℕ) :
    ((1 + C c * X : ℂ⟦X⟧)^d)⁻¹ =
      rescale (-c) (invOneSubPow ℂ d).val := by
  apply (inv_eq_iff_mul_eq_one (by simp :
    constantCoeff ((1 + C c * X : ℂ⟦X⟧)^d) ≠ 0)).2
  have h := (invOneSubPow ℂ d).val_inv
  rw [invOneSubPow_inv_eq_one_sub_pow] at h
  have hh := congrArg (rescale (-c)) h
  simpa only [map_mul, map_pow, map_sub, map_one, rescale_X, map_neg,
    neg_mul, sub_neg_eq_add] using hh

private lemma coeff_inverse_linear_pow (c : ℂ) (d q : ℕ) (hd : 0 < d) :
    coeff q (((1 + C c * X : ℂ⟦X⟧)^d)⁻¹) =
      (-c)^q * ((d-1+q).choose (d-1) : ℂ) := by
  rw [inverse_linear_pow, coeff_rescale,
    invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℂ d hd, coeff_mk]

end D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo

namespace D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
open PowerSeries
private noncomputable def posTerm (c : ℂ) (n : ℕ) : ℂ⟦X⟧ :=
  X^n * (C c + X^n)^(2*n)
private noncomputable def negTerm (c : ℂ) (k : ℕ) : ℂ⟦X⟧ :=
  X^(2*k^2-k) * ((1+C c*X^k)^(2*k))⁻¹
private noncomputable def posVal (c : ℂ) (m n : ℕ) : ℂ :=
  c^(2*n-(m/n-1)) * ((2*n).choose (m/n-1) : ℂ)
private noncomputable def negVal (c : ℂ) (m k : ℕ) : ℂ :=
  if 2*k-1 ≤ m/k then (-c)^(m/k-(2*k-1)) * ((m/k).choose (2*k-1) : ℂ) else 0

private lemma posTerm_expand (c : ℂ) (n : ℕ) (hn : n ≠ 0) :
    posTerm c n = expand n hn (X * (C c + X)^(2*n)) := by
  simp [posTerm, expand_C]

private lemma inverse_linear_expand (c : ℂ) (d n : ℕ) (hn : n ≠ 0) :
    ((1+C c*X^n : ℂ⟦X⟧)^d)⁻¹ =
      expand n hn (((1+C c*X : ℂ⟦X⟧)^d)⁻¹) := by
  apply (inv_eq_iff_mul_eq_one (by simp [hn] :
    constantCoeff ((1+C c*X^n : ℂ⟦X⟧)^d) ≠ 0)).2
  have h := congrArg (expand n hn) (PowerSeries.inv_mul_cancel _ (by simp :
    constantCoeff ((1+C c*X : ℂ⟦X⟧)^d) ≠ 0))
  simpa only [map_mul, map_pow, map_add, map_one, expand_C, expand_X] using h

private lemma negTerm_expand (c : ℂ) (k : ℕ) (hk : k ≠ 0) :
    negTerm c k = expand k hk (X^(2*k-1) * ((1+C c*X)^(2*k))⁻¹) := by
  rw [negTerm, inverse_linear_expand c (2*k) k hk]
  simp only [map_mul, map_pow, expand_X]
  congr 1
  rw [← pow_mul]
  congr 1
  simp only [Nat.mul_sub_left_distrib, mul_one, pow_two]
  congr 1; ring

private lemma coeff_pos_mul (c : ℂ) (n q : ℕ) (hn : n ≠ 0) (hq : 0 < q) :
    coeff (n*q) (posTerm c n) = c^(2*n-(q-1)) * ((2*n).choose (q-1) : ℂ) := by
  rw [posTerm_expand c n hn, coeff_expand_mul]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  rw [coeff_succ_X_mul, coeff_C_add_X_pow]
  simp

private lemma coeff_neg_mul (c : ℂ) (k q : ℕ) (hk : k ≠ 0) :
    coeff (k*q) (negTerm c k) =
      if 2*k-1 ≤ q then (-c)^(q-(2*k-1)) * (q.choose (2*k-1) : ℂ) else 0 := by
  rw [negTerm_expand c k hk, coeff_expand_mul, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_inverse_linear_pow c (2*k) (q-(2*k-1)) (by omega)]
    rw [Nat.add_sub_of_le h]
  · rfl

private lemma coeff_pos_not_dvd (c : ℂ) (m n : ℕ) (hn : n ≠ 0) (h : ¬ n ∣ m) :
    coeff m (posTerm c n) = 0 := by
  rw [posTerm_expand c n hn, coeff_expand_of_not_dvd n hn _ h]

private lemma coeff_neg_not_dvd (c : ℂ) (m k : ℕ) (hk : k ≠ 0) (h : ¬ k ∣ m) :
    coeff m (negTerm c k) = 0 := by
  rw [negTerm_expand c k hk, coeff_expand_of_not_dvd k hk _ h]

end D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo

set_option autoImplicit false
namespace D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
open PowerSeries
private lemma coeffA_divisors (c : ℂ) (m : ℕ) (hm : 0 < m) :
    D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA c m =
      (∑ n ∈ m.divisors, posVal c m n) + ∑ k ∈ m.divisors, negVal c m k := by
  classical
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hp : (∑ n ∈ Finset.range (m+1), coeff m (posTerm c n)) =
      ∑ n ∈ m.divisors, posVal c m n := by
    calc
      _ = ∑ n ∈ m.divisors, coeff m (posTerm c n) := by
        symm
        apply Finset.sum_subset
        · intro n hn
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le
            (Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hn)))
        · intro n hn hnd
          by_cases hn0 : n = 0
          · subst n
            simp [posTerm, hm0]
          · apply coeff_pos_not_dvd c m n hn0
            intro hd
            exact hnd (Nat.mem_divisors.mpr ⟨hd,hm0⟩)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        have hd := Nat.dvd_of_mem_divisors hn
        have hnpos := Nat.pos_of_mem_divisors hn
        have hnle := Nat.le_of_dvd hm hd
        have hq : 0 < m/n := Nat.div_pos hnle hnpos
        have h := coeff_pos_mul c n (m/n) (Nat.ne_of_gt hnpos) hq
        simpa only [Nat.mul_div_cancel' hd, posVal] using h
  have hn : (∑ k ∈ Finset.Icc 1 m, coeff m (negTerm c k)) =
      ∑ k ∈ m.divisors, negVal c m k := by
    calc
      _ = ∑ k ∈ m.divisors, coeff m (negTerm c k) := by
        symm
        apply Finset.sum_subset
        · intro k hk
          exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hk,
            Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hk)⟩
        · intro k hk hkd
          apply coeff_neg_not_dvd c m k (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)
          intro hd
          exact hkd (Nat.mem_divisors.mpr ⟨hd,hm0⟩)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hd := Nat.dvd_of_mem_divisors hk
        have h := coeff_neg_mul c k (m/k) (Nat.ne_of_gt (Nat.pos_of_mem_divisors hk))
        simpa only [Nat.mul_div_cancel' hd, negVal] using h
  exact congrArg₂ (· + ·) hp hn

theorem coeffA_prime (c : ℂ) (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA c p = p*c^(p-1) + c^(2*p) := by
  rw [coeffA_divisors c p hp.pos, hp.divisors]
  have hne : 1 ≠ p := hp.ne_one.symm
  have hch : (2 : ℕ).choose (p-1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have he : Even (p-1) := hp.even_sub_one (by omega)
  have hneg : (-c)^(p-1) = c^(p-1) := he.neg_pow c
  have hdiv : p/p = 1 := Nat.div_self hp.pos
  have hnot : ¬ p ≤ 1 := not_le.mpr hp.one_lt
  have hle : 1 ≤ p := Nat.one_le_of_lt h3
  simp [Finset.sum_pair hne, posVal, negVal, hdiv, hch, hnot, hle, hneg,
    Nat.choose_one_right]
  ring
end D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo

set_option autoImplicit false
namespace D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
private lemma vals_pair (c : ℂ) (m n k : ℕ) (hk : 0 < k)
    (hq : m/n = 2*k) (hq' : m/k = 2*n) :
    posVal c m n + negVal c m k = 0 := by
  unfold posVal negVal
  rw [hq, hq']
  by_cases h : 2*k-1 ≤ 2*n
  · rw [ite_eq_left h]
    have ho : Odd (2*n-(2*k-1)) := ⟨n-k, by omega⟩
    rw [ho.neg_pow]
    ring
  · rw [ite_eq_right h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma dyadic_quotients (N i : ℕ) (hi : i < N) :
    2^N / 2^i = 2*2^(N-1-i) ∧ 2^N / 2^(N-1-i) = 2*2^i := by
  constructor
  · rw [Nat.pow_div (Nat.le_of_lt hi) (by norm_num : 0 < (2:ℕ)),
      show N-i = (N-1-i)+1 by omega, pow_succ']
  · rw [Nat.pow_div (show N-1-i ≤ N by omega) (by norm_num : 0 < (2:ℕ)),
      show N-(N-1-i) = i+1 by omega, pow_succ']

theorem coeffA_pow_two (c : ℂ) (N : ℕ) (hN : 0 < N) :
    D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA c (2^N) = c^(2^(N+1)) := by
  rw [coeffA_divisors c (2^N) (by positivity)]
  simp_rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h2 : 2 ≤ (2:ℕ)^N := Nat.le_pow hN
  have hp : posVal c (2^N) (2^N) = c^(2^(N+1)) := by
    simp [posVal, Nat.div_self (by positivity : 0 < (2:ℕ)^N), pow_succ, mul_comm]
  have hn : negVal c (2^N) (2^N) = 0 := by
    simp [negVal, Nat.div_self (by positivity : 0 < (2:ℕ)^N), show ¬ 2*2^N-1 ≤ 1 by omega]
  have hs : (∑ i ∈ Finset.range N, posVal c (2^N) (2^i)) +
      (∑ i ∈ Finset.range N, negVal c (2^N) (2^i)) = 0 := by
    rw [← Finset.sum_range_reflect (fun i => negVal c (2^N) (2^i)) N]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨hq, hq'⟩ := dyadic_quotients N i (Finset.mem_range.mp hi)
    apply vals_pair c (2^N) (2^i) (2^(N-1-i)) (by positivity) hq hq'
  rw [hp,hn]
  linear_combination hs
end D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo

namespace D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
theorem result : claim := by
  intro n hn
  change coeffA 2 (2^n) = _
  rw [D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_pow_two 2 n hn, pow_succ', pow_mul]
  norm_num
end D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
