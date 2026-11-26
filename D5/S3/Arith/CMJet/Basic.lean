/- GID: D5/S3/Arith/CMJet/Basic
   generality: G
   mirror-B: none(waiver:cm-jet-native-arithmetic)
   mirror-E: none(waiver:cm-jet-native-arithmetic)
   anchors: []
   utility: none
   digest: The polynomial-pair lemniscatic algebra has an integral derivation, explicit iterates, support, and the factorial top jet. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-! The polynomial-pair algebra of the lemniscate and its integral derivation. -/

noncomputable section

namespace D5.S3.Arith.CMJet

open Polynomial
open scoped Polynomial

variable {A : Type*} [CommRing A]

def W (A : Type*) [CommRing A] : A[X] := 1 - X ^ 4

abbrev Curve (A : Type*) [CommRing A] := QuadraticAlgebra A[X] (W A) 0

def poly (f : A[X]) : Curve A := ⟨f, 0⟩
def yPoly (g : A[X]) : Curve A := ⟨0, g⟩

def x (A : Type*) [CommRing A] : Curve A := poly X
def y (A : Type*) [CommRing A] : Curve A := yPoly 1

@[simp] lemma poly_re (f : A[X]) : (poly f).re = f := rfl
@[simp] lemma poly_im (f : A[X]) : (poly f).im = 0 := rfl
@[simp] lemma yPoly_re (g : A[X]) : (yPoly g).re = 0 := rfl
@[simp] lemma yPoly_im (g : A[X]) : (yPoly g).im = g := rfl

lemma pair_decompose (z : Curve A) : z = poly z.re + y A * poly z.im := by
  apply QuadraticAlgebra.ext <;> simp [y]

lemma x_pow (n : ℕ) : (x A) ^ n = poly (X ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ih]; apply QuadraticAlgebra.ext <;> simp [x]

lemma poly_aeval (f : A[X]) : aeval (x A) f = poly f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, hf, hg]; apply QuadraticAlgebra.ext <;> simp
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C, x_pow]
      apply QuadraticAlgebra.ext <;>
        simp [Algebra.algebraMap_eq_smul_one, Polynomial.smul_eq_C_mul]

lemma y_sq : y A ^ 2 = poly (W A) := by
  apply QuadraticAlgebra.ext <;> simp [pow_two, y]

/-- The invariant derivation in the basis \(1,Y\), with \(Y^2=1-X^4\). -/
def D (A : Type*) [CommRing A] : Derivation A (Curve A) (Curve A) where
  toLinearMap :=
    { toFun := fun z => ⟨W A * z.im.derivative - 2 * X ^ 3 * z.im, z.re.derivative⟩
      map_add' := by
        intro z w
        apply QuadraticAlgebra.ext <;> simp [mul_add] <;> ring
      map_smul' := by
        intro r z
        apply QuadraticAlgebra.ext <;> simp [derivative_smul, Polynomial.smul_eq_C_mul] <;> ring }
  map_one_eq_zero' := by
    apply QuadraticAlgebra.ext
    · change W A * (0 : A[X]).derivative - 2 * X ^ 3 * 0 = 0
      simp
    · change (1 : A[X]).derivative = 0
      simp
  leibniz' := by
    intro z w
    apply QuadraticAlgebra.ext <;>
      dsimp
    · simp [smul_eq_mul, derivative_add, derivative_mul, W,
        derivative_sub, derivative_X_pow] <;> ring
    · simp [smul_eq_mul, derivative_add, derivative_mul]
      rw [show (W A).derivative = -4 * X ^ 3 by
        simp only [W, derivative_sub, derivative_one, derivative_X_pow]
        norm_num [Polynomial.C_ofNat]]
      ring

@[simp] lemma D_re (z : Curve A) :
    (D A z).re = W A * z.im.derivative - 2 * X ^ 3 * z.im := rfl

@[simp] lemma D_im (z : Curve A) : (D A z).im = z.re.derivative := rfl

@[simp] lemma D_poly (f : A[X]) : D A (poly f) = yPoly f.derivative := by
  apply QuadraticAlgebra.ext <;> simp

@[simp] lemma D_yPoly (g : A[X]) :
    D A (yPoly g) = poly (W A * g.derivative - 2 * X ^ 3 * g) := by
  apply QuadraticAlgebra.ext <;> simp

@[simp] lemma D_x : D A (x A) = y A := by simp [x, y]
@[simp] lemma D_y : D A (y A) = poly (-2 * X ^ 3) := by
  apply QuadraticAlgebra.ext <;> simp [y, neg_mul]

def iter (n : ℕ) : Module.End A (Curve A) := (D A).toLinearMap ^ n

lemma iter_eq (n : ℕ) (z : Curve A) : iter n z = (D A)^[n] z :=
  Module.End.pow_apply _ _ _

@[simp] lemma iter_zero (z : Curve A) : iter 0 z = z := rfl

lemma iter_succ (n : ℕ) (z : Curve A) : iter (n + 1) z = D A (iter n z) := by
  simp only [iter_eq, Function.iterate_succ_apply']

lemma iter_add (m n : ℕ) (z : Curve A) : iter (m + n) z = iter m (iter n z) := by
  simp only [iter_eq, Function.iterate_add_apply]

lemma iter_one (z : Curve A) : iter 1 z = D A z := by rw [iter_succ, iter_zero]

/-- The square of the invariant derivation on the polynomial summand. -/
def Q (f : A[X]) : A[X] := W A * f.derivative.derivative - 2 * X ^ 3 * f.derivative

@[simp] lemma iter_two_poly (f : A[X]) : iter 2 (poly f) = poly (Q f) := by
  change iter (1 + 1) (poly f) = _
  rw [iter_add]
  simp [iter_one, Q]

lemma iter_even_poly (n : ℕ) (f : A[X]) : iter (2 * n) (poly f) = poly (Q^[n] f) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, iter_add, ih, iter_two_poly,
        Function.iterate_succ_apply']

lemma Q_C_mul (a : A) (f : A[X]) : Q (C a * f) = C a * Q f := by
  simp [Q, derivative_C_mul] <;> ring

lemma Q_sub (f g : A[X]) : Q (f - g) = Q f - Q g := by
  simp [Q, derivative_sub] <;> ring

lemma Q_X_pow (k : ℕ) :
    Q (X ^ k : A[X]) =
      C ((k : A) * ((k : A) - 1)) * X ^ (k - 2) -
      C ((k : A) * ((k : A) + 1)) * X ^ (k + 2) := by
  by_cases hk : 2 ≤ k
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h₁ : (2 + l - 1 : ℕ) = l + 1 := by omega
    have h₂ : (l + 1 - 1 : ℕ) = l := by omega
    have h₃ : (2 + l - 2 : ℕ) = l := by omega
    have h₄ : (2 + l + 2 : ℕ) = l + 4 := by omega
    simp only [Q, W, derivative_X_pow, derivative_C_mul, h₁, h₂, h₃, h₄,
      Nat.cast_add, Nat.cast_two, Nat.cast_one]
    simp only [pow_add X l 4, pow_succ X l, map_mul, map_add, map_sub, map_one, map_ofNat]
    ring
  · interval_cases k <;> norm_num [Q, W, derivative_X_pow, derivative_C_mul,
      Polynomial.C_ofNat] <;> push_cast <;> ring

/-- The three terms of the fourth derivative, with integer-style coefficient subtraction. -/
lemma iter_four_X_pow (k : ℕ) :
    iter 4 (poly (X ^ k : A[X])) = poly
      (C ((k : A) * ((k : A) - 1) * ((k : A) - 2) * ((k : A) - 3)) * X ^ (k - 4) -
       C (2 * (k : A)^2 * ((k : A)^2 + 5)) * X ^ k +
       C ((k : A) * ((k : A) + 1) * ((k : A) + 2) * ((k : A) + 3)) * X ^ (k + 4)) := by
  change iter (2 + 2) (poly (X ^ k : A[X])) = _
  rw [iter_add, iter_two_poly, iter_two_poly]
  congr 1
  rw [Q_X_pow, Q_sub, Q_C_mul, Q_C_mul, Q_X_pow, Q_X_pow]
  by_cases hk : 4 ≤ k
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp only [show (4 + l - 2 : ℕ) = l + 2 by omega,
      show (l + 2 - 2 : ℕ) = l by omega,
      show (4 + l + 2 - 2 : ℕ) = 4 + l by omega,
      show (4 + l - 4 : ℕ) = l by omega,
      show l + 2 + 2 = 4 + l by omega,
      show 4 + l + 2 + 2 = 4 + l + 4 by omega]
    push_cast
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one]
    ring
  · interval_cases k <;> norm_num [Q, W, derivative_X_pow, derivative_C_mul,
      Polynomial.C_ofNat] <;> push_cast <;> ring

lemma Q_coeff (f : A[X]) (n : ℕ) :
    (Q f).coeff n =
      f.coeff (n + 2) * (↑(n + 2) : A) * (↑(n + 1) : A) -
      if 2 ≤ n then f.coeff (n - 2) * (↑(n - 2) : A) * (↑(n - 1) : A) else 0 := by
  have hc : (2 : A[X]) = C (2 : A) := (Polynomial.C_ofNat 2).symm
  rw [Q, W, sub_mul, one_mul, hc, mul_assoc]
  simp only [coeff_sub, coeff_C_mul, coeff_X_pow_mul', coeff_derivative]
  by_cases hn : 4 ≤ n
  · rw [if_pos hn, if_pos (by omega : 3 ≤ n), if_pos (by omega : 2 ≤ n)]
    rw [show n - 4 + 1 + 1 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega,
      show n - 3 + 1 = n - 2 by omega]
    have h : n - 1 = n - 3 + 2 := by omega
    rw [h]
    have h4 : ((n - 4 : ℕ) : A) + 1 = ((n - 3 : ℕ) : A) := by
      calc
        ((n - 4 : ℕ) : A) + 1 = ((n - 4 + 1 : ℕ) : A) := by
          rw [Nat.cast_add]
          simp
        _ = ((n - 3 : ℕ) : A) := by congr 1 <;> omega
    have h3 : ((n - 3 : ℕ) : A) + 1 = ((n - 2 : ℕ) : A) := by
      calc
        ((n - 3 : ℕ) : A) + 1 = ((n - 3 + 1 : ℕ) : A) := by
          rw [Nat.cast_add]
          simp
        _ = ((n - 2 : ℕ) : A) := by congr 1 <;> omega
    rw [h4, h3]
    push_cast
    ring
  · interval_cases n <;> norm_num <;> ring

/-- Each square of the derivation shifts monomial exponents by two modulo four. -/
lemma Q_iter_monomial_support (s r n : ℕ) (hn : n % 4 ≠ (2 * s + r) % 4) :
    (Q^[s] (X ^ r : A[X])).coeff n = 0 := by
  induction s generalizing n with
  | zero =>
      have h : n ≠ r := by omega
      simp [coeff_X_pow, h]
  | succ s ih =>
      rw [Function.iterate_succ_apply', Q_coeff, ih (n + 2) (by omega)]
      split_ifs with h
      · rw [ih (n - 2) (by omega)]; simp
      · simp

lemma Q_iter_X_degree (s n : ℕ) (hn : 2 * s + 1 < n) :
    (Q^[s] (X : A[X])).coeff n = 0 := by
  induction s generalizing n with
  | zero =>
      have h : n ≠ 1 := by omega
      simp [coeff_X, Ne.symm h]
  | succ s ih =>
      rw [Function.iterate_succ_apply', Q_coeff, ih (n + 2) (by omega),
        if_pos (by omega : 2 ≤ n), ih (n - 2) (by omega)]
      simp

/-- Evaluation at \(O=(0,1)\). -/
def atO : Curve A →ₗ[A] A where
  toFun z := z.re.coeff 0 + z.im.coeff 0
  map_add' z w := by simp <;> ring
  map_smul' a z := by simp [coeff_smul, mul_add]

@[simp] lemma atO_apply (z : Curve A) : atO z = z.re.coeff 0 + z.im.coeff 0 := rfl

lemma atO_mul (u v : Curve A) : atO (u * v) = atO u * atO v := by
  simp [mul_coeff_zero, W, coeff_X_pow] <;> ring

lemma odd_jet (s : ℕ) (f : A[X]) :
    atO (iter (2 * s + 1) (poly f)) = (Q^[s] f).coeff 1 := by
  rw [show 2 * s + 1 = 1 + 2 * s by omega, iter_add, iter_one, iter_even_poly, D_poly]
  simp [coeff_derivative]

/-- Below the lowest possible exponent, every coefficient of the even jet vanishes. -/
lemma Q_iter_low (s r k : ℕ) (hk : k + 2 * s < r) :
    (Q^[s] (X ^ r : A[X])).coeff k = 0 := by
  induction s generalizing k with
  | zero => simp [coeff_X_pow, show k ≠ r by omega]
  | succ s ih =>
      rw [Function.iterate_succ_apply', Q_coeff, ih (k + 2) (by omega)]
      split_ifs with h
      · rw [ih (k - 2) (by omega)]; simp
      · simp

lemma ascFactorial_first (a n : ℕ) :
    a.ascFactorial (n + 1) = a * (a + 1).ascFactorial n := by
  induction n with
  | zero => simp [Nat.ascFactorial_succ]
  | succ n ih =>
      rw [Nat.ascFactorial_succ, ih, Nat.ascFactorial_succ]
      ring

/-- At the lowest possible exponent the unique descending term gives the factorial ratio. -/
lemma Q_iter_lowest (s k : ℕ) :
    (Q^[s] (X ^ (k + 2 * s) : A[X])).coeff k = ↑((k + 1).ascFactorial (2 * s)) := by
  induction s generalizing k with
  | zero => simp
  | succ s ih =>
      rw [Function.iterate_succ_apply', Q_coeff]
      have he : k + 2 * (s + 1) = k + 2 + 2 * s := by omega
      have hlow : (if 2 ≤ k then
          (Q^[s] (X ^ (k + 2 * (s + 1)) : A[X])).coeff (k - 2) *
            (↑(k - 2) : A) * (↑(k - 1) : A) else 0) = 0 := by
        split_ifs with hk
        · rw [Q_iter_low s _ _ (by omega)]; simp
        · rfl
      rw [hlow, sub_zero, he, ih (k + 2)]
      rw [show 2 * (s + 1) = (2 * s + 1) + 1 by omega]
      rw [ascFactorial_first, ascFactorial_first]
      push_cast
      ring

theorem odd_top_jet (s : ℕ) :
    atO (iter (2 * s + 1) (poly (X ^ (2 * s + 1) : A[X]))) = ↑(2 * s + 1).factorial := by
  rw [odd_jet, show 2 * s + 1 = 1 + 2 * s by omega, Q_iter_lowest]
  have h := Nat.factorial_mul_ascFactorial 1 (2 * s)
  simpa using congrArg (fun n : ℕ => (n : A)) h

end D5.S3.Arith.CMJet
