/- GID: D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A binomial-square recurrence computes two integer power-series transforms. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19311
admission_basis: escape-witness (square_binomial_sum)
escape_witness: square_binomial_sum (binomial-square recurrence induction)
Direct frozen dependencies: D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.map_inverse.
This is a declaration address; no module pin is used as a declaration identity.
The rational summands and coefficient claims use the source expressions unchanged.
Declaration assessment (definitions have no proof_shape):
  den_mul: bind-only; consumers: den_rescale.
  map_den: bind-only; consumers: map_term.
  Q: definition; consumers: HannaLegendreCentralBinomialModFour.series4_eq, HannaLegendreCentralBinomialModFour.Q_two, HannaLegendreCentralBinomialModFour.term_reduction_four, HannaLegendreCentralBinomialModThree.series3_eq, Q_coeff, summand, term_low, map_Q, map_term, Q_zero, reduced_term_coeff.
  Q_coeff: bind-only; consumers: HannaLegendreCentralBinomialModFour.Q_two, map_Q, Q_zero.
  summand: definition; consumers: HannaLegendreCentralBinomialModFour.series4_eq, HannaLegendreCentralBinomialModFour.integral4, HannaLegendreCentralBinomialModFour.term_reduction_four, HannaLegendreCentralBinomialModFour.coefficient_reduction_four, HannaLegendreCentralBinomialModFour.map_source_four, HannaLegendreCentralBinomialModFour.map_R_four, HannaLegendreCentralBinomialModFour.integer_coefficient_reduction_four, HannaLegendreCentralBinomialModFour.R_mod_four, HannaLegendreCentralBinomialModFour.source_residue_four, HannaLegendreCentralBinomialModFour.result, HannaLegendreCentralBinomialModThree.series3_eq, HannaLegendreCentralBinomialModThree.integral3, HannaLegendreCentralBinomialModThree.R_mod_three, HannaLegendreCentralBinomialModThree.mod_three_series, HannaLegendreCentralBinomialModThree.result, term_low, weighted, map_term, map_weighted, reduced_term_coeff, R_coeff, T_coeff.
  term_low: bind-only; consumers: HannaLegendreCentralBinomialModFour.coefficient_reduction_four.
  weighted: definition; consumers: HannaLegendreCentralBinomialModFour.coefficient_reduction_four, HannaLegendreCentralBinomialModFour.map_T2_four, HannaLegendreCentralBinomialModFour.integer_coefficient_reduction_four, HannaLegendreCentralBinomialModFour.square_moment_mod_two, HannaLegendreCentralBinomialModFour.twice_T2_four, HannaLegendreCentralBinomialModFour.source_residue_four, map_weighted, T_coeff, T_odd, T_even, T_mod_two.
  map_Q: bind-only; consumers: map_term.
  map_term: bind-only; consumers: map_weighted.
  map_weighted: bind-only; consumers: HannaLegendreCentralBinomialModFour.map_T2_four, HannaLegendreCentralBinomialModFour.square_moment_mod_two, map_series.
  map_series: bind-only; consumers: HannaLegendreCentralBinomialModFour.integral4, HannaLegendreCentralBinomialModFour.map_source_four, HannaLegendreCentralBinomialModFour.map_R_four, HannaLegendreCentralBinomialModThree.integral3, HannaLegendreCentralBinomialModThree.mod_three_series.
  den_rescale: bind-only; consumers: den_coeff.
  den_coeff: bind-only; consumers: reduced_term_coeff.
  Q_zero: bind-only; consumers: HannaLegendreCentralBinomialModFour.term_reduction_four, reduced_term_coeff.
  rational_den: bind-only; consumers: HannaLegendreCentralBinomialModFour.series4_eq, HannaLegendreCentralBinomialModThree.series3_eq.
  certificate: bind-only; consumers: F_recurrence.
  F: definition; consumers: F_recurrence, square_binomial_sum.
  F_recurrence: bind-only; consumers: square_binomial_sum.
  square_binomial_sum: content; consumers: reduced_term_coeff.
  coeff_one_add_pow: bind-only; consumers: coeff_one_sub_pow, alternating_square, weighted_alternating_coefficient.
  coeff_one_sub_pow: bind-only; consumers: alternating_square, weighted_alternating_coefficient, coeff_one_sub_sq_pow.
  alternating_square: bind-only; consumers: R_coeff.
  weighted_alternating_coefficient: bind-only; consumers: weighted_alternating_succ.
  weighted_alternating_succ: bind-only; consumers: weighted_alternating_odd, weighted_alternating_even.
  reduced_term_coeff: content; consumers: R_coeff, T_coeff.
  R_coeff: content; consumers: HannaLegendreCentralBinomialModFour.R_mod_four, HannaLegendreCentralBinomialModThree.R_mod_three.
  coeff_one_sub_sq_pow: bind-only; consumers: weighted_alternating_odd, weighted_alternating_even.
  weighted_alternating_odd: bind-only; consumers: T_odd.
  weighted_alternating_even: bind-only; consumers: T_even.
  T_coeff: content; consumers: T_odd, T_even, T_mod_two.
  T_odd: content; consumers: T_mod_two.
  T_even: content; consumers: T_mod_two.
  T_mod_two: content; consumers: HannaLegendreCentralBinomialModFour.twice_T2_four.
-/

import D5.S1.Recurrence.Residue.ContinuedFractionOddSquare
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform
open PowerSeries Finset

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem den_mul (c : R) (n : ℕ) : (invOfUnit ((1 - C c * X)^(2*n+1)) 1) * (1 - C c * X)^(2*n+1) = 1 := by
  exact invOfUnit_mul _ _ (by simp)

private theorem map_den (hom : R →+* S) (c : R) (n : ℕ) :
    ((invOfUnit ((1 - C c * X)^(2*n+1)) 1)).map hom = (invOfUnit ((1 - C (hom c) * X)^(2*n+1)) 1) := by
  have h := D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.map_inverse hom ((1 - C c * X)^(2*n+1)) (by simp)
  change (invOfUnit ((1 - C c * X)^(2*n+1)) 1).map hom =
    invOfUnit (((1 - C c * X)^(2*n+1)).map hom) 1 at h
  rw [map_pow, map_sub, map_one, map_mul, map_C, map_X] at h
  exact h

noncomputable def Q (a : R) (n : ℕ) : PowerSeries R :=
  ∑ k ∈ Finset.range (n+1), C ((n.choose k : R)^2 * a^k) * X^k

theorem Q_coeff (a : R) (n k : ℕ) :
    coeff k (Q a n) = (n.choose k : R)^2 * a^k := by
  simp only [Q, map_sum, coeff_C_mul_X_pow]
  simp +contextual [Nat.choose_eq_zero_of_lt]

noncomputable def summand (c a b : R) (n : ℕ) : PowerSeries R :=
  X^n * (invOfUnit ((1 - C c * X)^(2*n+1)) 1) * Q a n * Q b n

theorem term_low (c a b : R) (n k : ℕ) (hk : k < n) :
    coeff k (summand c a b n) = 0 := by
  unfold summand
  rw [mul_assoc, mul_assoc, coeff_X_pow_mul']
  simp [Nat.not_le.mpr hk]

noncomputable def weighted (w : ℕ → R) (c a b : R) : PowerSeries R :=
  mk fun m => coeff m (∑ n ∈ Finset.range (m+1), C (w n) * summand c a b n)


private theorem map_Q (hom : R →+* S) (a : R) (n : ℕ) :
    (Q a n).map hom = Q (hom a) n := by
  ext k
  rw [coeff_map, Q_coeff, Q_coeff]
  simp

private theorem map_term (hom : R →+* S) (c a b : R) (n : ℕ) :
    (summand c a b n).map hom = summand (hom c) (hom a) (hom b) n := by
  simp [summand, map_den, map_Q]

theorem map_weighted (hom : R →+* S) (w : ℕ → R) (c a b : R) :
    (weighted w c a b).map hom = weighted (fun n => hom (w n)) (hom c) (hom a) (hom b) := by
  ext m
  simp only [coeff_map, weighted, coeff_mk]
  rw [← coeff_map]
  apply congrArg (coeff m)
  simp only [map_sum, map_mul, map_C, map_term]

theorem map_series (hom : R →+* S) (c a b : R) :
    (weighted (Function.const ℕ 1) c a b).map hom = weighted (Function.const ℕ 1) (hom c) (hom a) (hom b) := by
  rw [map_weighted]
  congr 1
  funext n
  exact hom.map_one

private theorem den_rescale (c : R) (n : ℕ) :
    (invOfUnit ((1 - C c * X)^(2*n+1)) 1) = rescale c (invOneSubPow R (2*n+1)) := by
  have hu : IsUnit ((1 - C c * X : PowerSeries R)^(2*n+1)) := by
    rw [isUnit_iff_constantCoeff]
    simp
  apply hu.mul_right_cancel
  rw [den_mul]
  have h := congrArg (rescale c) (mk_add_choose_mul_one_sub_pow_eq_one R (2*n))
  simpa only [map_mul, map_pow, map_sub, map_one, rescale_X,
    invOneSubPow_val_succ_eq_mk_add_choose] using h.symm

private theorem den_coeff (c : R) (n r : ℕ) :
    coeff r ((invOfUnit ((1 - C c * X)^(2*n+1)) 1)) = c^r * ((2*n+r).choose (2*n) : R) := by
  rw [den_rescale, coeff_rescale]
  simp only [invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]

theorem Q_zero (n : ℕ) : Q (0:R) n = 1 := by
  ext k
  rw [Q_coeff]
  cases k <;> simp

theorem rational_den (c : ℚ) (n : ℕ) :
    (invOfUnit ((1 - C c * X)^(2*n+1)) 1) = ((1 - C c * X : PowerSeries ℚ)^(2*n+1))⁻¹ := by
  exact invOfUnit_eq' _ _ (by simp)

/-- A denominator-free form of the telescoping certificate. -/
private theorem certificate (n t k : ℕ) (hk : k ≤ n) :
    ((t + 1 : ℤ)^2) * (n.choose k : ℤ)^2 * ((2*n+t+1-k).choose (2*n) : ℤ) -
      ((n+t+1 : ℤ)^2) * (n.choose k : ℤ)^2 * ((2*n+t-k).choose (2*n) : ℤ) =
    -((k+1 : ℤ)^2) * (n.choose (k+1) : ℤ)^2 * ((2*n+t-k).choose (2*n) : ℤ) +
      (k : ℤ)^2 * (n.choose k : ℤ)^2 * ((2*n+t+1-k).choose (2*n) : ℤ) := by
  have hc : (n.choose (k+1) : ℤ) * ((k : ℤ)+1) =
      (n.choose k : ℤ) * ((n : ℤ)-k) := by
    exact_mod_cast (Nat.choose_succ_right_eq n k)
  have hnext : 2*n+t-k+1 = 2*n+t+1-k := by omega
  by_cases hkt : k ≤ t+1
  · have hb := Nat.choose_mul_succ_eq (2*n+t-k) (2*n)
    rw [hnext] at hb
    have htop : 2*n ≤ 2*n+t+1-k := by omega
    have hb' : ((2*n+t-k).choose (2*n) : ℤ) * ((2*(n:ℤ)+t+1-k)) =
        ((2*n+t+1-k).choose (2*n) : ℤ) * ((t:ℤ)+1-k) := by
      have hbz := congrArg (fun a : ℕ => (a : ℤ)) hb
      push_cast [Nat.cast_sub htop, Nat.cast_sub (show k ≤ 2*n+t+1 by omega)] at hbz
      convert hbz using 1 <;> ring
    have hc2 := congrArg (fun z : ℤ => z^2) hc
    linear_combination -(n.choose k : ℤ)^2 * ((t:ℤ)+1+k) * hb' +
      ((2*n+t-k).choose (2*n) : ℤ) * hc2
  · have h0 : (2*n+t-k).choose (2*n) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : (2*n+t+1-k).choose (2*n) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0, h1]

private noncomputable def F (n t : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (n.choose k : ℤ)^2 * ((2*n+t-k).choose (2*n) : ℤ)

private theorem F_recurrence (n t : ℕ) :
    ((t+1 : ℤ)^2) * F n (t+1) = ((n+t+1 : ℤ)^2) * F n t := by
  let G (k : ℕ) : ℤ := -(k:ℤ)^2 * (n.choose k : ℤ)^2 *
    ((2*n+t+1-k).choose (2*n) : ℤ)
  have hs : ((t+1 : ℤ)^2) * F n (t+1) - ((n+t+1 : ℤ)^2) * F n t =
      ∑ k ∈ range (n+1), (G (k+1) - G k) := by
    simp only [F, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    have h := certificate n t k (by simpa using mem_range.mp hk)
    dsimp [G]
    rw [show 2*n+t+1-(k+1) = 2*n+t-k by omega]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, mul_assoc, neg_mul, sub_neg_eq_add] using h
  have htel := sum_range_sub G (n+1)
  rw [htel] at hs
  have hg0 : G 0 = 0 := by simp [G]
  have hgn : G (n+1) = 0 := by simp [G, Nat.choose_succ_self]
  rw [hg0, hgn, sub_self] at hs
  exact sub_eq_zero.mp hs

theorem square_binomial_sum (n t : ℕ) :
    (∑ k ∈ range (n+1), (n.choose k : ℤ)^2 * ((2*n+t-k).choose (2*n) : ℤ)) =
      ((n+t).choose n : ℤ)^2 := by
  change F n t = _
  induction t with
  | zero =>
    have h : F n 0 = 1 := by
      unfold F
      rw [sum_eq_single 0]
      · simp
      · intro k hk hk0
        have htop : 2*n-k < 2*n := by
          have := mem_range.mp hk
          omega
        simp only [Nat.add_zero, Nat.choose_eq_zero_of_lt htop, Nat.cast_zero, mul_zero]
      · simp
    simpa using h
  | succ t ih =>
    have hr := F_recurrence n t
    rw [ih] at hr
    have hc := Nat.choose_mul_succ_eq (n+t) n
    have hc' : ((n+t+1).choose n : ℤ) * ((t:ℤ)+1) =
        ((n+t).choose n : ℤ) * ((n:ℤ)+t+1) := by
      have hz := congrArg (fun a : ℕ => (a:ℤ)) hc
      push_cast [Nat.cast_sub (show n ≤ n+t+1 by omega)] at hz
      nlinarith [hz]
    have ht : (0:ℤ) < (t:ℤ)+1 := by exact Int.succ_ofNat_pos t
    have heq : ((t:ℤ)+1)^2 *
        (F n (t+1) - ((n+t+1).choose n : ℤ)^2) = 0 := by
      have hc2 := congrArg (fun z : ℤ => z^2) hc'
      linear_combination hr - hc2
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ (ne_of_gt ht)))

private theorem coeff_one_add_pow (n k : ℕ) :
    coeff k ((1+X : PowerSeries ℤ)^n) = (n.choose k : ℤ) := by
  have hright : (1+X : PowerSeries ℤ)^n =
      ((1+Polynomial.X : Polynomial ℤ)^n).toPowerSeries := by simp
  rw [hright, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private theorem coeff_one_sub_pow (n k : ℕ) :
    coeff k ((1-X : PowerSeries ℤ)^n) = (-1:ℤ)^k * (n.choose k : ℤ) := by
  have he : (1-X : PowerSeries ℤ)^n = rescale (-1:ℤ) ((1+X)^n) := by
    simp only [map_pow, map_add, map_one, rescale_neg_one_X, sub_eq_add_neg]
  rw [he, coeff_rescale, coeff_one_add_pow]

private theorem alternating_square (N : ℕ) :
    (∑ n ∈ range (N+1), (-1:ℤ)^(N-n) * (N.choose n : ℤ)^2) =
      if 2 ∣ N then (-1:ℤ)^(N/2) * ((N).choose (N/2) : ℤ) else 0 := by
  have hprod : (1+X : PowerSeries ℤ)^N * (1-X)^N = (1-X^2)^N := by
    rw [← mul_pow]
    congr 1
    ring
  have he : (1-X^2 : PowerSeries ℤ)^N =
      expand 2 (by decide) ((1-X : PowerSeries ℤ)^N) := by
    simp
  have hh := congrArg (coeff N) hprod
  rw [he, coeff_expand] at hh
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  simp only [coeff_one_add_pow, coeff_one_sub_pow] at hh
  convert hh using 1
  apply sum_congr rfl
  intro n hn
  have hle : n ≤ N := by exact Finset.mem_range_succ_iff.mp hn
  rw [Nat.choose_symm hle]
  ring

private theorem weighted_alternating_coefficient (N : ℕ) :
    (∑ n ∈ range (N+1), (n:ℤ) * (-1:ℤ)^(N-n) * (N.choose n : ℤ)^2) =
    coeff N (X * derivative ((1+X : PowerSeries ℤ)^N) * (1-X)^N) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro n hn
  have hle : n ≤ N := by exact Finset.mem_range_succ_iff.mp hn
  rw [coeff_one_sub_pow, Nat.choose_symm hle]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_one_add_pow]
    push_cast
    ring

private theorem weighted_alternating_succ (N : ℕ) :
    (∑ n ∈ range (N+2), (n:ℤ) * (-1:ℤ)^(N+1-n) * ((N+1).choose n : ℤ)^2) =
    (N+1:ℤ) * (coeff N ((1-X^2 : PowerSeries ℤ)^N) -
      coeff N (X * (1-X^2 : PowerSeries ℤ)^N)) := by
  have h := weighted_alternating_coefficient (N+1)
  rw [derivative_pow] at h
  simp only [Nat.add_sub_cancel, map_add, derivative_one, derivative_X,
    zero_add, mul_one] at h
  have he : X * ((N+1 : PowerSeries ℤ) * (1+X)^N) * (1-X)^(N+1) =
      C (N+1:ℤ) * (X * ((1-X^2)^N - X * (1-X^2)^N)) := by
    have hp : (1+X : PowerSeries ℤ)^N * (1-X)^N = (1-X^2)^N := by
      rw [← mul_pow]
      congr 1
      ring
    calc
      _ = C (N+1:ℤ) * (X * ((1+X)^N * (1-X)^N) * (1-X)) := by
        rw [pow_succ]
        simp only [map_add, map_natCast, map_one]
        ring
      _ = _ := by rw [hp]; ring
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [he, coeff_C_mul, coeff_succ_X_mul, map_sub] at h
  simpa only [Nat.add_assoc] using h

private theorem reduced_term_coeff (N n : ℕ) (hn : n ≤ N) :
    coeff N (summand (-1:ℤ) (-1) 0 n) =
      (-1:ℤ)^(N-n) * (N.choose n : ℤ)^2 := by
  have hsum : coeff N (summand (-1:ℤ) (-1) 0 n) =
      (-1:ℤ)^(N-n) *
      (∑ k ∈ range (n+1), (n.choose k : ℤ)^2 * ((N+n-k).choose (2*n) : ℤ)) := by
    unfold summand
    rw [Q_zero, mul_one]
    simp only [Q, mul_sum, map_sum]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by exact Finset.mem_range_succ_iff.mp hk
    have hprod : X^n * (invOfUnit ((1 - C (-1:ℤ) * X)^(2*n+1)) 1) * (C ((n.choose k : ℤ)^2 * (-1)^k) * X^k) =
        C ((n.choose k : ℤ)^2 * (-1)^k) * (X^(n+k) * (invOfUnit ((1 - C (-1:ℤ) * X)^(2*n+1)) 1)) := by
      rw [pow_add]
      ring
    rw [hprod, coeff_C_mul, coeff_X_pow_mul']
    by_cases hnk : n+k ≤ N
    · rw [if_pos hnk, den_coeff]
      rw [show 2*n+(N-(n+k)) = N+n-k by omega]
      have hexp : N-n = k+(N-(n+k)) := by omega
      rw [hexp, pow_add]
      ring
    · have hzero : (N+n-k).choose (2*n) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hnk, hzero]
  rw [hsum]
  have hb := square_binomial_sum n (N-n)
  have he : n+(N-n) = N := by exact Nat.add_sub_of_le hn
  have ht : 2*n+(N-n) = N+n := by omega
  rw [he, ht] at hb
  rw [hb]


theorem R_coeff (N : ℕ) : coeff N (weighted (Function.const ℕ 1) (-1) (-1) 0) =
      if 2 ∣ N then (-1:ℤ)^(N/2) * (N.choose (N/2) : ℤ) else 0 := by
  simp only [weighted, coeff_mk, map_sum, Function.const_apply, map_one, one_mul]
  trans ∑ n ∈ range (N+1), (-1:ℤ)^(N-n) * (N.choose n : ℤ)^2
  · apply sum_congr rfl
    intro n hn
    exact reduced_term_coeff N n (by simpa using mem_range.mp hn)
  · exact alternating_square N

private theorem coeff_one_sub_sq_pow (n k : ℕ) :
    coeff k ((1-X^2 : PowerSeries ℤ)^n) =
      if 2 ∣ k then (-1:ℤ)^(k/2) * (n.choose (k/2) : ℤ) else 0 := by
  have he : (1-X^2 : PowerSeries ℤ)^n = expand 2 (by decide) ((1-X)^n) := by simp
  rw [he, coeff_expand]
  simp only [coeff_one_sub_pow]

private theorem weighted_alternating_odd (m : ℕ) :
    (∑ n ∈ range (2*m+2), (n:ℤ) * (-1:ℤ)^(2*m+1-n) * ((2*m+1).choose n : ℤ)^2) =
      (2*m+1:ℤ) * (-1:ℤ)^m * ((2*m).choose m : ℤ) := by
  have h := weighted_alternating_succ (2*m)
  have hx : coeff (2*m) (X * (1-X^2 : PowerSeries ℤ)^(2*m)) = 0 := by
    cases m with
    | zero => simp
    | succ m =>
      rw [show 2*(m+1) = 2*m+1+1 by omega, coeff_succ_X_mul, coeff_one_sub_sq_pow]
      simp [show ¬ 2 ∣ 2*m+1 by omega]
  rw [hx, sub_zero, coeff_one_sub_sq_pow] at h
  simpa only [dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, mul_assoc] using h

private theorem weighted_alternating_even (m : ℕ) :
    (∑ n ∈ range (2*m+3), (n:ℤ) * (-1:ℤ)^(2*m+2-n) * ((2*m+2).choose n : ℤ)^2) =
      -(2*m+2:ℤ) * (-1:ℤ)^m * ((2*m+1).choose m : ℤ) := by
  have h := weighted_alternating_succ (2*m+1)
  rw [coeff_succ_X_mul, coeff_one_sub_sq_pow, coeff_one_sub_sq_pow] at h
  simp only [show ¬ 2 ∣ 2*m+1 by omega, ite_false, dvd_mul_right, ite_true,
    Nat.mul_div_cancel_left _ (by decide : 0 < 2), zero_sub, mul_neg] at h
  convert h using 1 <;> push_cast <;> ring



private theorem T_coeff (N : ℕ) : coeff N (weighted (fun n => (n:ℤ)) (-1) (-1) 0) =
    ∑ n ∈ range (N+1), (n:ℤ) * (-1:ℤ)^(N-n) * (N.choose n : ℤ)^2 := by
  simp only [weighted, coeff_mk, map_sum, coeff_C_mul]
  apply sum_congr rfl
  intro n hn
  rw [reduced_term_coeff N n (by simpa using mem_range.mp hn)]
  ring

private theorem T_odd (m : ℕ) : coeff (2*m+1) (weighted (fun n => (n:ℤ)) (-1) (-1) 0) =
    (2*m+1:ℤ) * (-1:ℤ)^m * ((2*m).choose m : ℤ) := by
  rw [T_coeff]
  simpa only [Nat.add_assoc] using weighted_alternating_odd m

private theorem T_even (m : ℕ) : coeff (2*m+2) (weighted (fun n => (n:ℤ)) (-1) (-1) 0) =
    -(2*m+2:ℤ) * (-1:ℤ)^m * ((2*m+1).choose m : ℤ) := by
  rw [T_coeff]
  simpa only [Nat.add_assoc] using weighted_alternating_even m

theorem T_mod_two : (weighted (fun n => (n:ℤ)) (-1) (-1) 0).map (Int.castRingHom (ZMod 2)) = X := by
  ext N
  rw [coeff_map]
  rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
  · cases m with
    | zero => simp [T_coeff]
    | succ m =>
      rw [show 2*(m+1) = 2*m+2 by omega, T_even]
      simp [Int.coe_castRingHom, coeff_X, show (2:ZMod 2) = 0 by decide,
        show 2*m+2 ≠ 1 by omega]
  · rw [T_odd]
    by_cases hm0 : m = 0
    · subst m
      norm_num
    · have hz : ((2*m).choose m : ZMod 2) = 0 := by
        apply (ZMod.natCast_eq_zero_iff _ _).mpr
        exact Nat.two_dvd_centralBinom_of_one_le (Nat.pos_of_ne_zero hm0)
      simp [hz, coeff_X, hm0]

end D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform
