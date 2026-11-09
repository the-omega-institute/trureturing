/- GID: D5/S3/ArithSums/MatharA386829
   generality: I
   mirror-B: D5/B/S3/ArithSums/MatharA386829
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Mathar's recurrence and a homogeneous formal differential equation for A386829. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Inclusive binomial transformation, telescoping recurrence, and formal differential equation. -/

namespace D5.S3.ArithSums.MatharA386829
open scoped BigOperators
open Finset

/-- The literal inclusive finite sum defining OEIS A386829. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (3 : ℤ)^k * 2^(n-k) *
    ((2*n+1).choose k : ℤ) * ((2*n-k).choose (n-k) : ℤ)

private def b (n : ℕ) : ℤ :=
  ∑ j ∈ range (n + 1), (5 : ℤ)^j * 3^(n-j) * ((n+j).choose j : ℤ)

private def c (n : ℕ) : ℤ := (5 : ℤ)^n * ((2*n).choose n : ℤ)

private theorem choose_product (n i j : ℕ) (hij : i ≤ j) :
    ((n+j).choose j : ℤ) * (j.choose i : ℤ) =
      ((n+i).choose i : ℤ) * ((n+j).choose (n+i) : ℤ) := by
  have h := Nat.choose_mul (n := n+j) (k := n+i) (s := n) (by omega)
  rw [show n+j-n = j by omega, show n+i-n = i by omega,
    Nat.choose_symm_add, Nat.choose_symm_add] at h
  exact_mod_cast h.symm.trans (Nat.mul_comm _ _)

private theorem hockey (n i : ℕ) (hi : i ≤ n) :
    (∑ j ∈ Ico i (n+1), ((n+j).choose (n+i) : ℤ)) =
      ((2*n+1).choose (n-i) : ℤ) := by
  rw [sum_Ico_eq_sum_range]
  have hlen : n+1-i = n-i+1 := by omega
  rw [hlen]
  have h := Nat.sum_range_add_choose (n-i) (n+i)
  have hs : (∑ j ∈ range (n-i+1), ((n+(i+j)).choose (n+i) : ℤ)) =
      (((n-i)+(n+i)+1).choose (n+i+1) : ℤ) := by
    exact_mod_cast (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
  rw [hs]
  congr 1
  have ht : n-i+(n+i)+1 = 2*n+1 := by omega
  rw [ht]
  exact Nat.choose_symm_of_eq_add (by omega)

private theorem literal_eq_auxiliary (n : ℕ) : a n = b n := by
  have expand : b n = ∑ j ∈ range (n+1), ∑ i ∈ range (j+1),
      (2 : ℤ)^i * 3^(n-i) * ((n+j).choose j : ℤ) * (j.choose i : ℤ) := by
    unfold b
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using mem_range.mp hj
    rw [show (5 : ℤ) = 2+3 by norm_num, add_pow, sum_mul, sum_mul]
    apply sum_congr rfl
    intro i hi
    have hij : i ≤ j := by simpa using mem_range.mp hi
    have hp : (3 : ℤ)^(j-i) * 3^(n-j) = 3^(n-i) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      _ = (2 : ℤ)^i * (3^(j-i) * 3^(n-j)) * ((n+j).choose j : ℤ) * (j.choose i : ℤ) := by ring
      _ = _ := by rw [hp]
  have swap := sum_Ico_Ico_comm 0 (n+1)
    (fun i j => (2 : ℤ)^i * 3^(n-i) * ((n+j).choose j : ℤ) * (j.choose i : ℤ))
  simp only [← range_eq_Ico] at swap
  have hb : b n = ∑ i ∈ range (n+1),
      (2 : ℤ)^i * 3^(n-i) * ((n+i).choose i : ℤ) * ((2*n+1).choose (n-i) : ℤ) := by
    rw [expand, ← swap]
    apply sum_congr rfl
    intro i hi
    have hin : i ≤ n := by simpa using mem_range.mp hi
    calc
      _ = ∑ j ∈ Ico i (n+1),
          (2 : ℤ)^i * 3^(n-i) * ((n+i).choose i : ℤ) * ((n+j).choose (n+i) : ℤ) := by
        apply sum_congr rfl
        intro j hj
        rw [mul_assoc, choose_product n i j (mem_Ico.mp hj).1]
        ring
      _ = _ := by rw [← mul_sum, hockey n i hin]
  rw [hb]
  unfold a
  rw [← sum_range_reflect (fun k => (3 : ℤ)^k * 2^(n-k) *
    ((2*n+1).choose k : ℤ) * ((2*n-k).choose (n-k) : ℤ)) (n+1)]
  apply sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using mem_range.mp hi
  have h1 : n+1-1-i = n-i := by omega
  have h2 : n-(n-i) = i := by omega
  have h3 : 2*n-(n-i) = n+i := by omega
  rw [h1, h2, h3]
  ring

private theorem auxiliary_step (n : ℕ) :
    4*b (n+1) + 18*b n = 7*c (n+1) := by
  let U : ℕ → ℤ := fun k =>
    6 * 5^k * 3^(n+1-k) * ((n+k).choose (k-1) : ℤ)
  have telescoping : ∀ k ∈ range (n+1),
      (if k = 0 then U (k+1) else U (k+1)-U k) =
        4*((5 : ℤ)^k * 3^(n+1-k) * ((n+1+k).choose k : ℤ)) +
        18*((5 : ℤ)^k * 3^(n-k) * ((n+k).choose k : ℤ)) := by
    intro k hk
    have hkn : k ≤ n := by simpa using mem_range.mp hk
    cases k with
    | zero => simp [U, pow_succ]; ring
    | succ k =>
      rw [ite_eq_right (by omega)]
      simp only [U, Nat.succ_sub_one]
      rw [show n+1-(k+1+1) = n-k-1 by omega,
        show n+1-(k+1) = n-k by omega]
      have hp : (3 : ℤ)^(n-k) = 3 * 3^(n-k-1) := by
        rw [← pow_succ']; congr 1; omega
      have hp' : (3 : ℤ)^(n-(k+1)) = 3^(n-k-1) := by congr 1
      rw [hp', hp]
      have hpas := Nat.choose_succ_succ (n+k+1) k
      have hpas' : ((n+1+(k+1)).choose (k+1) : ℤ) =
          ((n+(k+1)).choose k : ℤ) + ((n+(k+1)).choose (k+1) : ℤ) := by
        exact_mod_cast (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpas)
      simp only [Nat.add_left_comm, Nat.add_comm] at hpas' ⊢
      rw [hpas']
      simp only [pow_succ]
      ring
  have hs := sum_congr rfl telescoping
  have htel : (∑ k ∈ range (n+1), if k = 0 then U (k+1) else U (k+1)-U k) = U (n+1) := by
    rw [sum_range_succ']
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    rw [sum_range_sub (fun i => U (i+1)) n]
    ring
  rw [htel, sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  have hc : U (n+1) = 3*c (n+1) := by
    have hchoose : (2*(n+1)).choose (n+1) = 2 * (2*n+1).choose n := by
      rw [show 2*(n+1) = (2*n+1)+1 by omega, Nat.choose_succ_succ,
        Nat.choose_symm_half]
      omega
    simp only [U, c, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    rw [show n+(n+1) = 2*n+1 by omega, hchoose, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hb : b (n+1) = (∑ k ∈ range (n+1),
      (5 : ℤ)^k * 3^(n+1-k) * ((n+1+k).choose k : ℤ)) + c (n+1) := by
    unfold b c
    rw [sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [show n+1+(n+1) = 2*(n+1) by omega]
  change U (n+1) = 4*(∑ k ∈ range (n+1),
    (5 : ℤ)^k * 3^(n+1-k) * ((n+1+k).choose k : ℤ)) + 18*b n at hs
  rw [hc] at hs
  linarith

private theorem central_step (n : ℕ) :
    (n+1 : ℤ)*c (n+1) = 10*(2*n+1)*c n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have hz : (n+1 : ℤ) * ((2*(n+1)).choose (n+1) : ℤ) =
      2*(2*n+1)*((2*n).choose n : ℤ) := by exact_mod_cast h
  unfold c
  rw [pow_succ]
  linear_combination (5 : ℤ)^(n+1) * hz

private theorem recurrence (n : ℕ) :
    2*(n+2 : ℤ)*a (n+2) + (20-31*(n+2 : ℤ))*a (n+1) +
      90*(1-2*(n+2 : ℤ))*a n = 0 := by
  rw [literal_eq_auxiliary, literal_eq_auxiliary, literal_eq_auxiliary]
  have h1 := auxiliary_step (n+1)
  have h0 := auxiliary_step n
  have hc := central_step (n+1)
  simp only [Nat.add_assoc] at h1 hc
  push_cast at h1 hc
  have htwice : 2*(2*(n+2 : ℤ)*b (n+2) + (20-31*(n+2 : ℤ))*b (n+1) +
      90*(1-2*(n+2 : ℤ))*b n) = 0 := by
    linear_combination (n+2 : ℤ)*h1 - 10*(2*n+3 : ℤ)*h0 + 7*hc
  omega

/-- The entire ordinary formal generating series over the rationals. -/
noncomputable def series : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)

private theorem formal_equation :
    (2 - 31*PowerSeries.X - 180*PowerSeries.X^2) *
        PowerSeries.derivative series - (11 + 270*PowerSeries.X)*series = PowerSeries.C 15 := by
  open PowerSeries in
  ext n
  cases n with
  | zero =>
    simp only [sub_mul, add_mul, pow_two, mul_assoc, map_sub, map_add,
      coeff_ofNat_mul, coeff_zero_X_mul, coeff_derivative, series, coeff_mk,
      coeff_C, ite_true]
    norm_num [a, Finset.sum_range_succ, Nat.choose]
  | succ n =>
    cases n with
    | zero =>
      simp only [sub_mul, add_mul, pow_two, mul_assoc, map_sub, map_add,
        coeff_ofNat_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_derivative,
        series, coeff_mk, coeff_C, Nat.succ_ne_zero, ite_false]
      norm_num [a, Finset.sum_range_succ, Nat.choose]
    | succ n =>
      have h := recurrence (n+1)
      have hq : 2*(n+1+2 : ℚ)*(a (n+1+2) : ℚ) +
          (20-31*(n+1+2 : ℚ))*(a (n+1+1) : ℚ) +
          90*(1-2*(n+1+2 : ℚ))*(a (n+1) : ℚ) = 0 := by exact_mod_cast h
      simp only [sub_mul, add_mul, pow_two, mul_assoc, map_sub, map_add,
        coeff_succ_X_mul, coeff_ofNat_mul, coeff_derivative, series, coeff_mk,
        coeff_C, Nat.succ_ne_zero, ite_false]
      simp only [Nat.add_assoc] at hq ⊢
      push_cast at hq ⊢
      linear_combination hq

private theorem homogeneous_equation :
    (2 - 31*PowerSeries.X - 180*PowerSeries.X^2) *
        PowerSeries.derivative (PowerSeries.derivative series) -
      (42 + 630*PowerSeries.X) * PowerSeries.derivative series - 270*series = 0 := by
  have h2 : PowerSeries.derivative (2 : PowerSeries ℚ) = 0 := PowerSeries.derivative_C
  have h31 : PowerSeries.derivative (31 : PowerSeries ℚ) = 0 := PowerSeries.derivative_C
  have h180 : PowerSeries.derivative (180 : PowerSeries ℚ) = 0 := PowerSeries.derivative_C
  have h11 : PowerSeries.derivative (11 : PowerSeries ℚ) = 0 := PowerSeries.derivative_C
  have h270 : PowerSeries.derivative (270 : PowerSeries ℚ) = 0 := PowerSeries.derivative_C
  have h := congrArg (PowerSeries.derivative (R := ℚ)) formal_equation
  simp only [map_sub, map_add, Derivation.leibniz, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, h2, h31, h180, h11, h270, PowerSeries.derivative_C, smul_eq_mul,
    mul_one] at h
  linear_combination h

/-- The full literal recurrence and a nonzero homogeneous polynomial differential equation. -/
theorem result :
    (∀ n : ℕ, 2 ≤ n →
      2*(n : ℤ)*a n + (20-31*(n : ℤ))*a (n-1) +
        90*(1-2*(n : ℤ))*a (n-2) = 0) ∧
    (∃ r : ℕ, ∃ p : ℕ → Polynomial ℚ,
      (∃ j ∈ range (r+1), p j ≠ 0) ∧
      ∑ j ∈ range (r+1), (p j : PowerSeries ℚ) *
        (PowerSeries.derivative (R := ℚ))^[j] series = 0) := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using recurrence m
  · let p : ℕ → Polynomial ℚ := fun j =>
      if j = 0 then -270 else if j = 1 then -(42+630*Polynomial.X)
      else 2-31*Polynomial.X-180*Polynomial.X^2
    refine ⟨2, p, ⟨2, by decide, ?_⟩, ?_⟩
    · intro h
      have hc := congrArg (fun q : Polynomial ℚ => q.coeff 0) h
      norm_num [p] at hc
    · simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Function.iterate_zero_apply, Function.iterate_succ_apply']
      simp only [show ¬(2 : ℕ) = 0 by decide, show ¬(2 : ℕ) = 1 by decide,
        show ¬(1 : ℕ) = 0 by decide, ite_true, ite_false,
        ← Polynomial.coeToPowerSeries.ringHom_apply, map_neg, map_sub, map_add,
        map_mul, map_pow, map_ofNat]
      simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      linear_combination homogeneous_equation

end D5.S3.ArithSums.MatharA386829
