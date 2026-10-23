/- GID: D5/S3/Arith/Congruence/CohnUniformThreeAdic
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/CohnUniformThreeAdic
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Uniform three-adic obstruction for the explicit Cohn polynomial. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Congruence.CohnUniformThreeAdic

open Polynomial Finset
open scoped QuadraticAlgebra

/-- The actual integral binomial polynomial, including its zero coefficients. -/
def cohnPolynomial (q : ℕ) : ℤ[X] :=
  ∑ k ∈ range ((q - 1) / 2 + 1),
    C ((q.choose (2 * k + 1) : ℤ) * (-3) ^ k) * (1 + X) ^ ((q - 1) / 2 - k)

private abbrev QP := QuadraticAlgebra ℤ[X] (-3) 0

private def z : QP := ⟨X, 1⟩

private def realPart (n : ℕ) : ℤ[X] := (z ^ n).re

private def sinePart (n : ℕ) : ℤ[X] := (z ^ n).im

private theorem real_step (n : ℕ) :
    realPart (n + 1) = X * realPart n - 3 * sinePart n := by
  simp [realPart, sinePart, pow_succ, z, sub_eq_add_neg, mul_comm, mul_left_comm]

private theorem sine_step (n : ℕ) :
    sinePart (n + 1) = realPart n + X * sinePart n := by
  simp [realPart, sinePart, pow_succ, z, mul_comm, add_comm]

private theorem coordinate_derivatives (n : ℕ) :
    derivative (realPart (n + 1)) = (n + 1 : ℤ[X]) * realPart n ∧
    derivative (sinePart (n + 1)) = (n + 1 : ℤ[X]) * sinePart n := by
  induction n with
  | zero => simp [realPart, sinePart, z]
  | succ n ih =>
      constructor
      · rw [real_step (n + 1), derivative_sub, derivative_mul,
          derivative_mul, derivative_X, derivative_ofNat, ih.1, ih.2,
          real_step n]
        push_cast
        ring
      · rw [sine_step (n + 1), derivative_add, derivative_mul,
          derivative_X, ih.1, ih.2, sine_step n]
        push_cast
        ring

private theorem sine_recurrence (n : ℕ) :
    sinePart (n + 2) = 2 * X * sinePart (n + 1) - (X ^ 2 + 3) * sinePart n := by
  rw [show n + 2 = (n + 1) + 1 by omega, sine_step (n + 1), real_step n,
    sine_step n]
  ring

private theorem sine_ode (n : ℕ) :
    (X ^ 2 + 3) * derivative (derivative (sinePart (n + 2))) -
      2 * (n + 1 : ℤ[X]) * X * derivative (sinePart (n + 2)) +
      (n + 2 : ℤ[X]) * (n + 1 : ℤ[X]) * sinePart (n + 2) = 0 := by
  have h₁ : derivative (sinePart (n + 2)) =
      (n + 2 : ℤ[X]) * sinePart (n + 1) := by
    simpa [Nat.cast_add, add_assoc, Nat.cast_one, one_add_one_eq_two] using
      (coordinate_derivatives (n + 1)).2
  have h₂ : derivative (derivative (sinePart (n + 2))) =
      (n + 2 : ℤ[X]) * (n + 1 : ℤ[X]) * sinePart n := by
    rw [h₁]
    simp only [derivative_mul, derivative_add, derivative_natCast, derivative_ofNat,
      zero_add, zero_mul, (coordinate_derivatives n).2]
    ring
  rw [h₂, h₁, sine_recurrence n]
  ring

/-- Binomial expansion in the quadratic algebra identifies the actual finite sum.
The paired sum proof includes the top odd summand and every even summand. -/
private theorem sine_odd_expansion (m : ℕ) :
    sinePart (2 * m + 1) =
      ∑ k ∈ range (m + 1),
        C (((2 * m + 1).choose (2 * k + 1) : ℤ) * (-3) ^ k) *
          X ^ (2 * (m - k)) := by
  let w : QP := QuadraticAlgebra.omega
  let a : QP := QuadraticAlgebra.C X
  have hz : z = w + a := by ext <;> simp [z, w, a, QuadraticAlgebra.omega]
  have hw : w ^ 2 = QuadraticAlgebra.C (-3) := by
    ext <;> norm_num [w, pow_two, QuadraticAlgebra.omega]
  have heven (k : ℕ) : w ^ (2 * k) = QuadraticAlgebra.C ((-3) ^ k) := by
    rw [pow_mul, hw, ← QuadraticAlgebra.C_pow]
  have hodd (k : ℕ) : w ^ (2 * k + 1) =
      (⟨0, (-3) ^ k⟩ : QP) := by
    rw [pow_succ, heven]
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_C, QuadraticAlgebra.im_C, w, QuadraticAlgebra.omega,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
  have hpairs (f : ℕ → ℤ[X]) (N : ℕ) :
      ∑ i ∈ range (2 * N), f i =
        ∑ k ∈ range N, (f (2 * k) + f (2 * k + 1)) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
          sum_range_succ, sum_range_succ, ih, sum_range_succ]
        abel
  have hexp := congrArg QuadraticAlgebra.im (add_pow w a (2 * m + 1))
  have himsum (s : Finset ℕ) (f : ℕ → QP) :
      (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
    exact map_sum (QuadraticAlgebra.imₗ (-3) 0 : QP →ₗ[ℤ[X]] ℤ[X]) f s
  rw [← hz] at hexp
  change sinePart (2 * m + 1) = _ at hexp
  rw [himsum, show 2 * m + 1 + 1 = 2 * (m + 1) by omega, hpairs] at hexp
  rw [hexp]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
  have hsub : 2 * m + 1 - (2 * k + 1) = 2 * (m - k) := by omega
  simp only [heven, hodd, a, ← QuadraticAlgebra.C_pow, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.re_C, QuadraticAlgebra.im_C,
    QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, zero_mul, mul_zero,
    zero_add, add_zero, hsub]
  simp only [C_mul, map_pow, map_neg, C_ofNat, C_eq_natCast]
  ring

private theorem polynomial_identification (m : ℕ) :
    (cohnPolynomial (2 * m + 1)).comp (X ^ 2 - 1) = sinePart (2 * m + 1) := by
  rw [sine_odd_expansion]
  simp only [cohnPolynomial, show (2 * m + 1 - 1) / 2 = m by omega,
    Polynomial.sum_comp, mul_comp, C_comp, pow_comp, add_comp, one_comp, X_comp]
  apply sum_congr rfl
  intro k hk
  rw [show (1 + (X ^ 2 - 1) : ℤ[X]) = X ^ 2 by ring, ← pow_mul]

private def evalQuadratic (x : ℤ) : QP →+* QuadraticAlgebra ℤ (-3) 0 where
  toFun u := ⟨u.re.eval x, u.im.eval x⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' u v := by ext <;> simp
  map_mul' u v := by ext <;> simp

private theorem sine_values (h : ℕ) :
    (sinePart (6 * h)).eval 1 = 0 ∧
      (sinePart (6 * h + 1)).eval 1 = 2 ^ (6 * h) := by
  let u : QuadraticAlgebra ℤ (-3) 0 := ⟨1, 1⟩
  have hu : u ^ 6 = QuadraticAlgebra.C 64 := by
    ext <;> norm_num [u, pow_succ]
  have hz : evalQuadratic 1 z = u := by ext <;> simp [evalQuadratic, z, u]
  have hpow : u ^ (6 * h) = QuadraticAlgebra.C (64 ^ h) := by
    rw [pow_mul, hu, ← QuadraticAlgebra.C_pow]
  have he (n : ℕ) : (sinePart n).eval 1 = (u ^ n).im := by
    have H := congrArg QuadraticAlgebra.im ((evalQuadratic 1).map_pow z n)
    rw [hz] at H
    exact H
  constructor
  · rw [he, hpow]
    rfl
  · rw [he, pow_succ, hpow]
    simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_C,
      QuadraticAlgebra.im_C, u, mul_one, zero_mul, add_zero]
    rw [pow_mul]
    norm_num

private theorem initial_coefficients (q : ℕ) (hq : q % 6 = 1) :
    (cohnPolynomial q).coeff 0 = 2 ^ (q - 1) ∧ (cohnPolynomial q).coeff 1 = 0 := by
  let h := q / 6
  have hq' : q = 6 * h + 1 := by dsimp [h]; omega
  have hodd : q = 2 * (3 * h) + 1 := by omega
  have hid : (cohnPolynomial q).comp (X ^ 2 - 1) = sinePart q := by
    rw [hodd]
    exact polynomial_identification _
  have h₀ := congrArg (eval (1 : ℤ)) hid
  have h₁ := congrArg (fun p : ℤ[X] => p.derivative.eval 1) hid
  have hval := sine_values h
  have hder : (sinePart q).derivative.eval 1 = 0 := by
    rw [hq', (coordinate_derivatives (6 * h)).2]
    simp [hval.1]
  constructor
  · simpa [eval_comp, ← coeff_zero_eq_eval_zero, hq', hval.2] using h₀
  · have hc : 2 * (cohnPolynomial q).coeff 1 = 0 := by
      simpa [derivative_comp, derivative_sub, derivative_pow, eval_comp,
        ← coeff_zero_eq_eval_zero, coeff_derivative, hder] using h₁
    omega

/-- The ODE is derived from the identified binomial polynomial, not postulated. -/
private theorem polynomial_ode (q : ℕ) (hq : 2 ≤ q) (hodd : q % 2 = 1) :
    4 * (X ^ 2 + 5 * X + 4) * derivative (derivative (cohnPolynomial q)) -
      2 * (((2 * q : ℤ[X]) - 3) * X + (2 * (q : ℤ[X]) - 6)) *
        derivative (cohnPolynomial q) +
      (q : ℤ[X]) * ((q : ℤ[X]) - 1) * cohnPolynomial q = 0 := by
  let P := cohnPolynomial q
  let g : ℤ[X] := X ^ 2 - 1
  have hqodd : q = 2 * ((q - 1) / 2) + 1 := by omega
  have hid : P.comp g = sinePart q := by
    simpa only [← hqodd] using polynomial_identification ((q - 1) / 2)
  have hs := sine_ode (q - 2)
  have hq2 : q - 2 + 2 = q := by omega
  simp only [hq2, Nat.cast_sub hq, Nat.cast_ofNat] at hs
  have hder₁ : derivative (sinePart q) = 2 * X * (derivative P).comp g := by
    rw [← hid, derivative_comp]
    simp [g, derivative_pow]
  have hder₂ : derivative (derivative (sinePart q)) =
      2 * (derivative P).comp g + 4 * X ^ 2 * (derivative (derivative P)).comp g := by
    rw [hder₁]
    simp only [derivative_mul, derivative_ofNat, derivative_X, derivative_comp,
      zero_mul, one_mul, zero_add]
    simp only [g, derivative_sub, derivative_pow, derivative_X, derivative_one,
      mul_one, sub_zero, Nat.reduceSub, pow_one, Nat.cast_ofNat, C_ofNat]
    ring
  rw [hder₂, hder₁, ← hid] at hs
  have hc :
      (4 * (X ^ 2 + 5 * X + 4) * derivative (derivative P) -
        2 * (((2 * q : ℤ[X]) - 3) * X + (2 * (q : ℤ[X]) - 6)) * derivative P +
        (q : ℤ[X]) * ((q : ℤ[X]) - 1) * P).comp g = 0 := by
    simp only [sub_comp, add_comp, mul_comp, pow_comp, X_comp,
      natCast_comp, ofNat_comp, one_comp]
    dsimp [g] at hs ⊢
    linear_combination hs
  rcases comp_eq_zero_iff.mp hc with H | H
  · exact H
  · have hf := congrArg (fun p : ℤ[X] => p.coeff 2) H.2
    norm_num [g, coeff_sub, coeff_X_pow] at hf

private def scaledCoeff (q r : ℕ) : ℤ :=
  (r.factorial : ℤ) * (cohnPolynomial q).coeff r

private theorem scaledCoeff_eq_derivative (q r : ℕ) :
    scaledCoeff q r = (derivative^[r] (cohnPolynomial q)).eval 0 := by
  simp [scaledCoeff, ← coeff_zero_eq_eval_zero, coeff_iterate_derivative,
    Nat.descFactorial_self, nsmul_eq_mul]

/-- All recurrence factors are integers. There is no bound on r. -/
private theorem scaled_recurrence (q : ℕ) (hq : 2 ≤ q) (hodd : q % 2 = 1) (r : ℕ) :
    16 * scaledCoeff q (r + 2) =
      4 * ((q : ℤ) - 5 * (r : ℤ) - 3) * scaledCoeff q (r + 1) -
        ((q : ℤ) - 2 * (r : ℤ)) * ((q : ℤ) - 2 * (r : ℤ) - 1) * scaledCoeff q r := by
  let P := cohnPolynomial q
  have ho := polynomial_ode q hq hodd
  have hnormal :
      C 4 * ((derivative^[2] P) * X ^ 2) +
        C 20 * (derivative (derivative P) * X) +
        C 16 * (derivative^[2] P) -
        C (2 * (2 * (q : ℤ) - 3)) * (derivative P * X) -
        C (4 * ((q : ℤ) - 3)) * derivative P +
        C ((q : ℤ) * ((q : ℤ) - 1)) * P = 0 := by
    dsimp [P]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      map_mul, map_sub, C_ofNat, C_eq_natCast, C_1]
    linear_combination ho
  have hxx : (derivative^[r] ((derivative^[2] P) * X ^ 2)).eval 0 =
      ((r * (r - 1) : ℕ) : ℤ) * (derivative^[r] P).eval 0 := by
    rw [iterate_derivative_derivative_mul_X_sq]
    simp [eval_smul, nsmul_eq_mul]
  have hx : (derivative^[r] (derivative P * X)).eval 0 =
      (r : ℤ) * (derivative^[r] P).eval 0 := by
    rw [iterate_derivative_derivative_mul_X]
    simp [eval_smul, nsmul_eq_mul]
  have hx' : (derivative^[r] (derivative (derivative P) * X)).eval 0 =
      (r : ℤ) * (derivative^[r + 1] P).eval 0 := by
    rw [iterate_derivative_derivative_mul_X]
    simp [eval_smul, nsmul_eq_mul, Function.iterate_succ_apply]
  have hnat : ((r * (r - 1) : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) - 1) := by
    cases r with
    | zero => norm_num
    | succ r => simp only [Nat.add_one_sub_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring
  have hd := congrArg (fun p : ℤ[X] => (derivative^[r] p).eval 0) hnormal
  simp only [iterate_map_add, iterate_derivative_sub, iterate_derivative_C_mul,
    eval_add, eval_sub, eval_mul, eval_C, hxx, hx, hx', hnat,
    iterate_derivative_zero, eval_zero, ← Function.iterate_add_apply,
    ← Function.iterate_succ_apply] at hd
  simp only [scaledCoeff_eq_derivative]
  dsimp [P] at hd
  simp only [Function.iterate_succ_apply]
  linear_combination hd

private theorem scaled_divisibility (q : ℕ) (hq : 7 ≤ q) (hq6 : q % 6 = 1) :
    ∀ r : ℕ, 1 ≤ r → (3 : ℤ) ^ padicValNat 3 (q - 1) ∣ scaledCoeff q r := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ν := padicValNat 3 (q - 1)
  have hodd : q % 2 = 1 := by omega
  have hinit := initial_coefficients q hq6
  have h₁ : scaledCoeff q 1 = 0 := by simp [scaledCoeff, hinit.2]
  have hqdiv : (3 : ℤ) ^ ν ∣ (q : ℤ) - 1 := by
    have h := (padicValNat_dvd_iff_le (p := 3) (by omega : q - 1 ≠ 0)).mpr
      (le_refl (padicValNat 3 (q - 1)))
    have hc : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]; norm_num
    rw [← hc]
    exact_mod_cast (show 3 ^ ν ∣ q - 1 from h)
  have cancel16 (a : ℤ) (ha : (3 : ℤ) ^ ν ∣ 16 * a) : (3 : ℤ) ^ ν ∣ a := by
    have hc : IsCoprime ((3 : ℤ) ^ ν) 16 := by
      exact (show IsCoprime (3 : ℤ) 16 by norm_num).pow_left
    exact hc.dvd_of_dvd_mul_left ha
  have h₂ : (3 : ℤ) ^ ν ∣ scaledCoeff q 2 := by
    apply cancel16
    have hrec := scaled_recurrence q (by omega) hodd 0
    simp only [Nat.zero_add, Nat.cast_zero, mul_zero, sub_zero, h₁, mul_zero,
      zero_sub] at hrec
    rw [hrec]
    exact (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqdiv (q : ℤ)) _).neg_right
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hr
      by_cases hr1 : r = 1
      · simp [hr1, h₁]
      by_cases hr2 : r = 2
      · simpa [hr2] using h₂
      have hr3 : 3 ≤ r := by omega
      have ha := ih (r - 2) (by omega) (by omega)
      have hb := ih (r - 1) (by omega) (by omega)
      apply cancel16
      have hrec := scaled_recurrence q (by omega) hodd (r - 2)
      rw [show r - 2 + 2 = r by omega, show r - 2 + 1 = r - 1 by omega] at hrec
      rw [hrec]
      exact (dvd_mul_of_dvd_right hb _).sub (dvd_mul_of_dvd_right ha _)

private theorem coefficient_term_dvd (q r : ℕ) (ξ : ℤ) (hr : 2 ≤ r)
    (hξ : (3 : ℤ) ∣ ξ)
    (hd : (3 : ℤ) ^ padicValNat 3 (q - 1) ∣ scaledCoeff q r) :
    (3 : ℤ) ^ (padicValNat 3 (q - 1) + 2) ∣ (cohnPolynomial q).coeff r * ξ ^ r := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hc : (cohnPolynomial q).coeff r = 0
  · simp [hc]
  by_cases hx : ξ = 0
  · simp [hx, Nat.ne_of_gt (by omega : 0 < r)]
  have hf : (r.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hprod : (r.factorial : ℤ) * (cohnPolynomial q).coeff r ≠ 0 := mul_ne_zero hf hc
  have hv := (padicValInt_dvd_iff (padicValNat 3 (q - 1))
    ((r.factorial : ℤ) * (cohnPolynomial q).coeff r)).mp hd
  have hv' : padicValNat 3 (q - 1) ≤
      padicValNat 3 r.factorial + padicValInt 3 ((cohnPolynomial q).coeff r) := by
    rcases hv with hv | hv
    · exact (hprod hv).elim
    · rw [padicValInt.mul hf hc, padicValInt.of_nat] at hv
      exact hv
  have hfact := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 3
    (by omega : r ≠ 0)
  have hfact' : padicValNat 3 r.factorial ≤ r - 2 := by
    norm_num only [Nat.reduceSub] at hfact
    omega
  have hpow : (3 : ℤ) ^ r ∣ ξ ^ r := pow_dvd_pow_of_dvd hξ r
  have hξr : ξ ^ r ≠ 0 := pow_ne_zero _ hx
  have hpv : r ≤ padicValInt 3 (ξ ^ r) := by
    rcases (padicValInt_dvd_iff r (ξ ^ r)).mp hpow with H | H
    · exact (hξr H).elim
    · exact H
  apply (padicValInt_dvd_iff _ _).mpr
  right
  rw [padicValInt.mul hc hξr]
  have hloss : padicValNat 3 r.factorial + 2 ≤ r := by omega
  calc
    padicValNat 3 (q - 1) + 2 ≤
        (padicValNat 3 r.factorial + padicValInt 3 ((cohnPolynomial q).coeff r)) + 2 :=
      Nat.add_le_add_right hv' 2
    _ = padicValInt 3 ((cohnPolynomial q).coeff r) + (padicValNat 3 r.factorial + 2) := by
      omega
    _ ≤ padicValInt 3 ((cohnPolynomial q).coeff r) + r := Nat.add_le_add_left hloss _
    _ ≤ padicValInt 3 ((cohnPolynomial q).coeff r) + padicValInt 3 (ξ ^ r) :=
      Nat.add_le_add_left hpv _

/-- For every q >= 7 congruent to 1 modulo 6, and every integer multiple ξ of 3,
the actual Cohn polynomial is congruent to 2^(q-1) modulo 3^(v₃(q-1)+2).
No primality assumption, coefficient recurrence hypothesis or degree cutoff occurs. -/
theorem cohn_stationary_congruence (q : ℕ) (ξ : ℤ) (hq : 7 ≤ q)
    (hq6 : q % 6 = 1) (hξ : (3 : ℤ) ∣ ξ) :
    (3 : ℤ) ^ (padicValNat 3 (q - 1) + 2) ∣
      (cohnPolynomial q).eval ξ - 2 ^ (q - 1) := by
  let P := cohnPolynomial q
  have hinit := initial_coefficients q hq6
  have hsum : P.eval ξ - P.coeff 0 =
      ∑ r ∈ P.support, (P.coeff r * ξ ^ r - if r = 0 then P.coeff r else 0) := by
    have heval : P.eval ξ = ∑ r ∈ P.support, P.coeff r * ξ ^ r := by
      conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
      simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [sum_sub_distrib, heval]
    congr 1
    by_cases hc : P.coeff 0 = 0
    · simp [hc]
    · simp [mem_support_iff.mpr hc]

  rw [← hinit.1]
  change (3 : ℤ) ^ (padicValNat 3 (q - 1) + 2) ∣ P.eval ξ - P.coeff 0
  rw [hsum]
  apply Finset.dvd_sum
  intro r hr
  by_cases hr0 : r = 0
  · simp [hr0]
  by_cases hr1 : r = 1
  · simp [hr1, P, hinit.2]
  simp only [if_neg hr0, sub_zero]
  exact coefficient_term_dvd q r ξ (by omega) hξ
    (scaled_divisibility q hq hq6 r (by omega))

/-- The actual equation P_q(ξ)=1 is impossible. LTE is applied at 4, 1 and (q-1)/2. -/
theorem cohn_polynomial_ne_one (q : ℕ) (ξ : ℤ) (hq : 7 ≤ q)
    (hq6 : q % 6 = 1) (hξ : (3 : ℤ) ∣ ξ) : (cohnPolynomial q).eval ξ ≠ 1 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let m := (q - 1) / 2
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hdouble : q - 1 = 2 * m := by dsimp [m]; omega
  have hLTE := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
    (by decide : Odd 3) (by norm_num : 1 < 4) (by norm_num : 3 ∣ 4 - 1)
    (by norm_num : ¬3 ∣ 4) hm
  have hν : padicValNat 3 (q - 1) = padicValNat 3 m := by
    rw [hdouble, padicValNat.mul (by norm_num : (2 : ℕ) ≠ 0) hm]
    rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬3 ∣ 2), zero_add]
  have hexp : (2 : ℕ) ^ (q - 1) = 4 ^ m := by
    rw [hdouble, pow_mul]
    norm_num
  have hv : padicValNat 3 (2 ^ (q - 1) - 1) = padicValNat 3 (q - 1) + 1 := by
    rw [hexp, hν]
    simpa only [one_pow, show padicValNat 3 (4 - 1) = 1 by norm_num,
      Nat.add_comm] using hLTE
  have hpos : 1 < (2 : ℕ) ^ (q - 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hn : (2 : ℕ) ^ (q - 1) - 1 ≠ 0 := by omega
  intro heq
  have hd := cohn_stationary_congruence q ξ hq hq6 hξ
  rw [heq] at hd
  have hd' : (3 : ℤ) ^ (padicValNat 3 (q - 1) + 2) ∣ (2 : ℤ) ^ (q - 1) - 1 := by
    simpa only [neg_sub] using hd.neg_right
  have hcast : (((2 : ℕ) ^ (q - 1) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (q - 1) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ (2 : ℕ) ^ (q - 1))]
    norm_cast
  rw [← hcast] at hd'
  have hdn : (3 : ℕ) ^ (padicValNat 3 (q - 1) + 2) ∣ 2 ^ (q - 1) - 1 := by
    exact_mod_cast hd'
  have hle := (padicValNat_dvd_iff_le hn).mp hdn
  rw [hv] at hle
  omega



namespace Exported
set_option backward.privateInPublic true in
export D5.S3.Arith.Congruence.CohnUniformThreeAdic (z sinePart polynomial_identification evalQuadratic)
end Exported

end D5.S3.Arith.Congruence.CohnUniformThreeAdic

