/- GID: D5/S3/ArithSums/MatharA386830
   generality: I
   mirror-B: D5/B/S3/ArithSums/MatharA386830
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Literal binomial sum and ordinary differential recurrence for OEIS A386830. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Finite binomial identities for the literal OEIS sequence and its ordinary formal series. -/

namespace D5.S3.ArithSums.MatharA386830
open scoped BigOperators
open Finset

/-- The inclusive integer NAME sum in OEIS A386830. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (3 : ℤ)^k * 2^(n-k) *
    ((3*n+1).choose k : ℤ) * ((3*n-k).choose (n-k) : ℤ)

private def f (N m : ℕ) : ℤ :=
  ∑ j ∈ range (m+1), (5 : ℤ)^j * (-2)^(m-j) * (N.choose j : ℤ)

private def t (n : ℕ) : ℤ := f (3*n+1) n

private theorem signed_partial (N M : ℕ) :
    (∑ r ∈ range (M+1), (-1 : ℤ)^(M-r) * ((N+1).choose r : ℤ)) =
      (N.choose M : ℤ) := by
  have hp (r : ℕ) (hr : r ≤ M) : (-1 : ℤ)^(M-r) = (-1)^M * (-1)^r := by
    have hsq : ((-1 : ℤ)^r)^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
      norm_num
    calc
      (-1 : ℤ)^(M-r) = (-1)^(M-r) * ((-1)^r)^2 := by rw [hsq, mul_one]
      _ = (-1)^M * (-1)^r := by
        rw [pow_two, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hr]
  calc
    _ = (-1 : ℤ)^M * ∑ r ∈ range (M+1), (-1)^r * ((N+1).choose r : ℤ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      rw [hp r (by simpa using mem_range.mp hr)]
      ring
    _ = _ := by
      rw [Int.alternating_sum_range_choose_eq_choose, ← mul_assoc, ← pow_two,
        ← pow_mul, Nat.mul_comm M 2, pow_mul]
      norm_num

private theorem literal_eq_transform (n : ℕ) : a n = t n := by
  have expand : t n = ∑ j ∈ range (n+1), ∑ k ∈ range (j+1),
      (3 : ℤ)^k * 2^(n-k) * (-1)^(n-j) *
        ((3*n+1).choose j : ℤ) * (j.choose k : ℤ) := by
    unfold t f
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using mem_range.mp hj
    rw [show (5 : ℤ) = 3+2 by norm_num, add_pow, sum_mul, sum_mul]
    apply sum_congr rfl
    intro k hk
    have hkj : k ≤ j := by simpa using mem_range.mp hk
    have hp : (2 : ℤ)^(j-k) * 2^(n-j) = 2^(n-k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [show (-2 : ℤ) = (-1)*2 by norm_num, mul_pow]
    calc
      _ = (3 : ℤ)^k * (2^(j-k) * 2^(n-j)) * (-1)^(n-j) *
          ((3*n+1).choose j : ℤ) * (j.choose k : ℤ) := by ring
      _ = _ := by rw [hp]
  have swap := sum_Ico_Ico_comm 0 (n+1)
    (fun k j => (3 : ℤ)^k * 2^(n-k) * (-1)^(n-j) *
      ((3*n+1).choose j : ℤ) * (j.choose k : ℤ))
  simp only [← range_eq_Ico] at swap
  rw [expand, ← swap]
  unfold a
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using mem_range.mp hk
  have inner : (∑ j ∈ Ico k (n+1), (-1 : ℤ)^(n-j) *
      (((3*n+1).choose j : ℤ) * (j.choose k : ℤ))) =
        ((3*n+1).choose k : ℤ) * ((3*n-k).choose (n-k) : ℤ) := by
    calc
      _ = ∑ j ∈ Ico k (n+1), (-1 : ℤ)^(n-j) *
          (((3*n+1).choose k : ℤ) * ((3*n+1-k).choose (j-k) : ℤ)) := by
        apply sum_congr rfl
        intro j hj
        rw [← Nat.cast_mul, Nat.choose_mul (mem_Ico.mp hj).1, Nat.cast_mul]
      _ = ((3*n+1).choose k : ℤ) * ∑ r ∈ range (n-k+1),
          (-1 : ℤ)^(n-k-r) * ((3*n-k+1).choose r : ℤ) := by
        rw [sum_Ico_eq_sum_range, show n+1-k = n-k+1 by omega, mul_sum]
        apply sum_congr rfl
        intro r hr
        rw [show n-(k+r) = n-k-r by omega, show k+r-k = r by omega,
          show 3*n+1-k = 3*n-k+1 by omega]
        ring
      _ = _ := by rw [signed_partial]
  calc
    _ = (3 : ℤ)^k * 2^(n-k) *
        (((3*n+1).choose k : ℤ) * ((3*n-k).choose (n-k) : ℤ)) := by ring
    _ = _ := by
      rw [← inner, mul_sum]
      apply sum_congr rfl
      intro j hj
      ring

private theorem f_geometric (N m : ℕ) :
    f N (m+1) + 2*f N m = (5 : ℤ)^(m+1) * (N.choose (m+1) : ℤ) := by
  have hs : (∑ j ∈ range (m+1), (5 : ℤ)^j * (-2)^(m+1-j) * (N.choose j : ℤ)) =
      -2 * f N m := by
    unfold f
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [show m+1-j = (m-j)+1 by have := mem_range.mp hj; omega, pow_succ]
    ring
  have hf : f N (m+1) =
      (∑ j ∈ range (m+1), (5 : ℤ)^j * (-2)^(m+1-j) * (N.choose j : ℤ)) +
      (5 : ℤ)^(m+1) * (N.choose (m+1) : ℤ) := by
    unfold f
    rw [sum_range_succ]
    simp
  rw [hf, hs]
  ring

private theorem f_pascal (N m : ℕ) :
    f (N+1) (m+1) = f N (m+1) + 5*f N m := by
  have hs : (∑ j ∈ range (m+1), (5 : ℤ)^(j+1) * (-2)^(m+1-(j+1)) *
      ((N+1).choose (j+1) : ℤ)) =
      (∑ j ∈ range (m+1), (5 : ℤ)^(j+1) * (-2)^(m+1-(j+1)) *
        (N.choose (j+1) : ℤ)) + 5*f N m := by
    unfold f
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right, pow_succ]
    ring
  unfold f at hs ⊢
  conv_lhs => rw [sum_range_succ']
  conv_rhs => arg 1; rw [sum_range_succ']
  rw [hs]
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, mul_one]
  ring

private theorem f_cubic (N m : ℕ) :
    4*f (N+3) (m+3) - 27*f N (m+2) =
      (5 : ℤ)^(m+3) * (4*(N.choose (m+3) : ℤ) +
        5*(N.choose (m+2) : ℤ) + 10*(N.choose (m+1) : ℤ)) := by
  have h0 := f_pascal (N+2) (m+2)
  have h1 := f_pascal (N+1) (m+2)
  have h2 := f_pascal (N+1) (m+1)
  have h3 := f_pascal N (m+2)
  have h4 := f_pascal N (m+1)
  have h5 := f_pascal N m
  have g0 := f_geometric N (m+2)
  have g1 := f_geometric N (m+1)
  have g2 := f_geometric N m
  simp only [Nat.add_assoc, pow_succ] at h0 h1 h2 h3 h4 h5 g0 g1 g2 ⊢
  linear_combination 4*h0 + 4*h1 + 20*h2 + 4*h3 + 40*h4 + 100*h5 +
    4*g0 + 25*g1 + 250*g2

private def b (n : ℕ) : ℤ := (5 : ℤ)^n * ((3*n-2).choose n : ℤ)

private theorem choose_boundary (n : ℕ) (hn : 2 ≤ n) :
    ((3*n-2).choose n : ℤ) = ((3*n-2).choose (n-1) : ℤ) +
      2*((3*n-2).choose (n-2) : ℤ) := by
  have h1 := Nat.choose_succ_right_eq (3*n-2) (n-1)
  have h2 := Nat.choose_succ_right_eq (3*n-2) (n-2)
  rw [show n-1+1 = n by omega, show 3*n-2-(n-1) = 2*n-1 by omega] at h1
  rw [show n-2+1 = n-1 by omega, show 3*n-2-(n-2) = 2*n by omega] at h2
  have hz1 : ((3*n-2).choose n : ℤ)*(n : ℤ) =
      ((3*n-2).choose (n-1) : ℤ)*((2*n-1 : ℕ) : ℤ) := by exact_mod_cast h1
  rw [Nat.cast_sub (by omega : 1 ≤ 2*n), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hz1
  have hz2 : ((3*n-2).choose (n-1) : ℤ)*((n-1 : ℕ) : ℤ) =
      ((3*n-2).choose (n-2) : ℤ)*(2*(n : ℤ)) := by exact_mod_cast h2
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hz2
  have h : (n : ℤ)*(((3*n-2).choose n : ℤ) -
      ((3*n-2).choose (n-1) : ℤ) - 2*((3*n-2).choose (n-2) : ℤ)) = 0 := by
    linear_combination hz1 + hz2
  have hnz : (n : ℤ) ≠ 0 := by omega
  have := (mul_eq_zero.mp h).resolve_left hnz
  linear_combination this

private theorem contiguous (n : ℕ) (hn : 1 ≤ n) :
    4*a n - 27*a (n-1) = 9*b n := by
  by_cases h1 : n = 1
  · subst n
    norm_num [a, b, sum_range_succ, Nat.choose]
  by_cases h2 : n = 2
  · subst n
    norm_num [a, b, sum_range_succ, Nat.choose]
  obtain ⟨m, rfl⟩ : ∃ m, n = m+3 := by exact ⟨n-3, by omega⟩
  have h := f_cubic (3*(m+3)-2) m
  have hc := choose_boundary (m+3) (by omega)
  rw [literal_eq_transform, literal_eq_transform]
  unfold t b
  rw [show m+3-1 = m+2 by omega,
    show 3*(m+3)+1 = (3*(m+3)-2)+3 by omega,
    show 3*(m+2)+1 = 3*(m+3)-2 by omega]
  have hchoose : ((3*(m+3)-2).choose (m+3) : ℤ) =
      ((3*(m+3)-2).choose (m+2) : ℤ) +
      2*((3*(m+3)-2).choose (m+1) : ℤ) := by simpa using hc
  linear_combination h - 5*(5 : ℤ)^(m+3)*hchoose

private theorem b_ratio (m : ℕ) :
    2*(m+2 : ℤ)*(2*(m+2 : ℤ)-3)*b (m+2) =
      15*(3*(m+2 : ℤ)-2)*(3*(m+2 : ℤ)-4)*b (m+1) := by
  have h1 := Nat.choose_mul_succ_eq (3*m+1) (m+1)
  have h2 := Nat.choose_mul_succ_eq (3*m+2) (m+1)
  have h3 := Nat.add_one_mul_choose_eq (3*m+3) (m+1)
  rw [show 3*m+1+1 = 3*m+2 by omega,
    show 3*m+1+1-(m+1) = 2*m+1 by omega] at h1
  rw [show 3*m+2+1 = 3*m+3 by omega,
    show 3*m+2+1-(m+1) = 2*m+2 by omega] at h2
  rw [show 3*m+3+1 = 3*m+4 by omega, show m+1+1 = m+2 by omega] at h3
  have z1 : ((3*m+1).choose (m+1) : ℤ)*(3*(m : ℤ)+2) =
      ((3*m+2).choose (m+1) : ℤ)*(2*(m : ℤ)+1) := by exact_mod_cast h1
  have z2 : ((3*m+2).choose (m+1) : ℤ)*(3*(m : ℤ)+3) =
      ((3*m+3).choose (m+1) : ℤ)*(2*(m : ℤ)+2) := by exact_mod_cast h2
  have z3 : (3*(m : ℤ)+4)*((3*m+3).choose (m+1) : ℤ) =
      ((3*m+4).choose (m+2) : ℤ)*((m : ℤ)+2) := by exact_mod_cast h3
  have hcancel : ((m : ℤ)+1) *
      (2*(2*(m : ℤ)+1)*((3*m+3).choose (m+1) : ℤ) -
        3*(3*(m : ℤ)+2)*((3*m+1).choose (m+1) : ℤ)) = 0 := by
    linear_combination -(2*(m : ℤ)+1)*z2 - 3*((m : ℤ)+1)*z1
  have hratio := (mul_eq_zero.mp hcancel).resolve_left (by omega : (m : ℤ)+1 ≠ 0)
  unfold b
  rw [show 3*(m+2)-2 = 3*m+4 by omega, show 3*(m+1)-2 = 3*m+1 by omega]
  simp only [pow_succ]
  linear_combination 5*(5 : ℤ)^m * 5 * (3*(m : ℤ)+4)*hratio -
    10*(5 : ℤ)^m * 5 * (2*(m : ℤ)+1)*z3

private theorem recurrence (m : ℕ) :
    8*(m+2 : ℤ)*(2*(m+2 : ℤ)-3)*a (m+2) +
      6*(-108*(m+2 : ℤ)^2+207*(m+2 : ℤ)-80)*a (m+1) +
      405*(3*(m+2 : ℤ)-2)*(3*(m+2 : ℤ)-4)*a m = 0 := by
  have h1 := contiguous (m+2) (by omega)
  have h0 := contiguous (m+1) (by omega)
  have hb := b_ratio m
  rw [show m+2-1 = m+1 by omega] at h1
  rw [show m+1-1 = m by omega] at h0
  linear_combination 2*((m : ℤ)+2)*(2*((m : ℤ)+2)-3)*h1 -
    15*(3*((m : ℤ)+2)-2)*(3*((m : ℤ)+2)-4)*h0 + 9*hb

/-- The entire ordinary rational formal series of the literal integer sum. -/
noncomputable def series : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)

private theorem homogeneous_equation :
    (16*PowerSeries.X - 648*PowerSeries.X^2 + 3645*PowerSeries.X^3) *
        PowerSeries.derivative (PowerSeries.derivative (PowerSeries.derivative series)) +
      (8 - 1998*PowerSeries.X + 21870*PowerSeries.X^2) *
        PowerSeries.derivative (PowerSeries.derivative series) +
      (-588 + 25110*PowerSeries.X) * PowerSeries.derivative series + 3240*series = 0 := by
  open PowerSeries in
  ext n
  have hq :
      8*(n+2 : ℚ)*(2*(n+2 : ℚ)-3)*(a (n+2) : ℚ) +
      6*(-108*(n+2 : ℚ)^2+207*(n+2 : ℚ)-80)*(a (n+1) : ℚ) +
      405*(3*(n+2 : ℚ)-2)*(3*(n+2 : ℚ)-4)*(a n : ℚ) = 0 := by
    exact_mod_cast recurrence n
  cases n with
  | zero =>
    simp only [sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc,
      map_sub, map_add, map_neg, map_zero, coeff_ofNat_mul, coeff_zero_X_mul,
      coeff_derivative, series, coeff_mk]
    norm_num at hq ⊢
    linear_combination hq
  | succ n =>
    cases n with
    | zero =>
      simp only [sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc,
        map_sub, map_add, map_neg, map_zero, coeff_ofNat_mul, coeff_zero_X_mul,
        coeff_succ_X_mul, coeff_derivative, series, coeff_mk]
      norm_num at hq ⊢
      linear_combination 2*hq
    | succ n =>
      cases n with
      | zero =>
        simp only [sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc,
          map_sub, map_add, map_neg, map_zero, coeff_ofNat_mul, coeff_zero_X_mul,
          coeff_succ_X_mul, coeff_derivative, series, coeff_mk]
        norm_num at hq ⊢
        linear_combination 3*hq
      | succ n =>
        simp only [sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc,
          map_sub, map_add, map_neg, map_zero, coeff_ofNat_mul, coeff_zero_X_mul,
          coeff_succ_X_mul, coeff_derivative, series, coeff_mk]
        simp only [Nat.succ_eq_add_one, Nat.add_assoc] at hq ⊢
        push_cast at hq ⊢
        linear_combination ((n : ℚ)+4)*hq

/-- The full literal recurrence and a nonzero homogeneous ordinary differential operator. -/
theorem result :
    (∀ n : ℕ, 2 ≤ n →
      8*(n : ℤ)*(2*(n : ℤ)-3)*a n +
      6*(-108*(n : ℤ)^2+207*(n : ℤ)-80)*a (n-1) +
      405*(3*(n : ℤ)-2)*(3*(n : ℤ)-4)*a (n-2) = 0) ∧
    (∃ r : ℕ, ∃ p : ℕ → Polynomial ℚ,
      (∃ j ∈ range (r+1), p j ≠ 0) ∧
      ∑ j ∈ range (r+1), (p j : PowerSeries ℚ) *
        (PowerSeries.derivative (R := ℚ))^[j] series = 0) := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
    simpa using recurrence m
  · let p : ℕ → Polynomial ℚ := fun j =>
      if j = 0 then 3240 else if j = 1 then -588+25110*Polynomial.X
      else if j = 2 then 8-1998*Polynomial.X+21870*Polynomial.X^2
      else 16*Polynomial.X-648*Polynomial.X^2+3645*Polynomial.X^3
    refine ⟨3, p, ⟨0, by decide, ?_⟩, ?_⟩
    · intro h
      have hc := congrArg (fun q : Polynomial ℚ => q.coeff 0) h
      norm_num [p] at hc
    · simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Function.iterate_zero_apply, Function.iterate_succ_apply']
      norm_num only [ite_true, ite_false, Nat.reduceEqDiff]
      simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_neg, map_sub, map_add,
        map_mul, map_pow, map_ofNat]
      simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      linear_combination homogeneous_equation

end D5.S3.ArithSums.MatharA386830
