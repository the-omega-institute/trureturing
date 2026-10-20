/- GID: D5/S3/Combinatorics/BinomialBases/SecondOrderStirlingTransform
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/SecondOrderStirlingTransform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The factorial-Stirling transform for every complex second-order recurrence. -/

import D5.S3.Combinatorics.ParisseStirlingFibonacciAlternatingSum
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Complex.Basic

open Finset Polynomial
open D5.S3.Combinatorics.ParisseStirlingFibonacciAlternatingSum (Q)

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform

private noncomputable def H : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => (1 + X) * H n + X * (1 + X) * derivative (H n)

private theorem row_coefficients (n k : ℕ) :
    (Q n).coeff k = (Nat.factorial k * Nat.stirlingSecond n k : ℕ) ∧
    (H n).coeff k = (Nat.factorial k * Nat.stirlingSecond (n + 1) (k + 1) : ℕ) := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [Q, H, coeff_one, Nat.stirlingSecond_succ_succ,
        Nat.stirlingSecond_zero_succ]
  | succ n ih =>
      have qrec : Q (n + 1) =
          X * derivative (Q n) + X * (X * derivative (Q n)) + X * Q n := by
        rw [Q]; ring
      have hrec : H (n + 1) =
          H n + X * H n + X * derivative (H n) + X * (X * derivative (H n)) := by
        rw [H]; ring
      constructor
      · rw [qrec]
        cases k with
        | zero => simp [mul_coeff_zero]
        | succ k =>
            cases k with
            | zero =>
                simp [coeff_X_mul, coeff_derivative, (ih _).1,
                  Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
            | succ k =>
                simp only [coeff_add, coeff_X_mul, coeff_derivative, (ih _).1,
                  Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul,
                  Nat.cast_succ, Nat.factorial_succ]
                ring
      · rw [hrec]
        cases k with
        | zero =>
            simp [mul_coeff_zero, (ih _).2, Nat.stirlingSecond_succ_succ]
        | succ k =>
            cases k with
            | zero =>
                simp [coeff_X_mul, coeff_derivative, mul_coeff_zero, (ih _).2,
                  Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
                ring
            | succ k =>
                simp only [coeff_add, coeff_X_mul, coeff_derivative, (ih _).2,
                  Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul,
                  Nat.cast_succ, Nat.factorial_succ]
                ring

private theorem reflection (n : ℕ) :
    (H n).comp (-1 - X) = C ((-1 : ℤ) ^ n) * Q n := by
  induction n with
  | zero => simp [H, Q]
  | succ n ih =>
      have di := congrArg derivative ih
      simp only [derivative_comp, derivative_sub, derivative_neg, derivative_one,
        derivative_X, derivative_C_mul] at di
      have di' : (derivative (H n)).comp (-1 - X) =
          -(C ((-1 : ℤ) ^ n) * derivative (Q n)) := by
        linear_combination -di
      rw [H, add_comp, mul_comp, mul_comp, mul_comp]
      simp only [add_comp, one_comp, X_comp, ih, di']
      rw [Q, pow_succ, C_mul]
      simp only [C_neg, C_1]
      ring

private theorem homogeneous_reflection (n : ℕ) :
    (∑ m ∈ range (n + 1),
      MvPolynomial.C ((Nat.factorial m * Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℤ) *
        (-MvPolynomial.X (1 : Fin 2) - MvPolynomial.X 0) ^ m *
        MvPolynomial.X 1 ^ (n - m)) =
    MvPolynomial.C ((-1 : ℤ) ^ n) *
      ∑ m ∈ range (n + 1),
        MvPolynomial.C ((Nat.factorial m * Nat.stirlingSecond n m : ℕ) : ℤ) *
          MvPolynomial.X (0 : Fin 2) ^ m * MvPolynomial.X 1 ^ (n - m) := by
  have qdeg : (Q n).natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [(row_coefficients n k).1, Nat.stirlingSecond_eq_zero_of_lt hk]
    simp
  have hdeg : (H n).natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [(row_coefficients n k).2,
      Nat.stirlingSecond_eq_zero_of_lt (show n + 1 < k + 1 by omega)]
    simp
  have hexp : H n = ∑ m ∈ range (n + 1),
      C ((Nat.factorial m * Nat.stirlingSecond (n + 1) (m + 1) : ℕ) : ℤ) * X ^ m := by
    simpa only [(row_coefficients n _).2] using
      (H n).as_sum_range_C_mul_X_pow' (show (H n).natDegree < n + 1 by omega)
  have qexp : Q n = ∑ m ∈ range (n + 1),
      C ((Nat.factorial m * Nat.stirlingSecond n m : ℕ) : ℤ) * X ^ m := by
    simpa only [(row_coefficients n _).1] using
      (Q n).as_sum_range_C_mul_X_pow' (show (Q n).natDegree < n + 1 by omega)
  have degree_one : (-1 - X : Polynomial ℤ).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have degree_pow (m : ℕ) : ((-1 - X : Polynomial ℤ) ^ m).natDegree ≤ m := by
    exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left m degree_one)
  have hp : ∀ m : ℕ, homogenize ((-1 - X : Polynomial ℤ) ^ m) m =
      (-MvPolynomial.X (1 : Fin 2) - MvPolynomial.X 0) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, homogenize_mul _ _ (degree_pow m) degree_one, ih]
        simp [homogenize_sub, homogenize_neg, homogenize_one, homogenize_X, pow_succ]
  have padded (m : ℕ) (hm : m ≤ n) : homogenize ((-1 - X : Polynomial ℤ) ^ m) n =
      (-MvPolynomial.X (1 : Fin 2) - MvPolynomial.X 0) ^ m *
        MvPolynomial.X 1 ^ (n - m) := by
    have h := homogenize_mul ((-1 - X : Polynomial ℤ) ^ m) 1
      (degree_pow m) (show (1 : Polynomial ℤ).natDegree ≤ n - m by simp)
    simpa [Nat.add_sub_of_le hm, hp] using h
  have r := reflection n
  rw [hexp, qexp] at r
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp] at r
  have hr := congrArg (fun f : Polynomial ℤ => homogenize f n) r
  simp only [homogenize_finsetSum, homogenize_C_mul] at hr
  convert hr using 1
  · apply sum_congr rfl
    intro m hm
    rw [padded m (by simpa using mem_range.mp hm)]
    ring
  · congr 1
    apply sum_congr rfl
    intro m hm
    rw [homogenize_X_pow (by simpa using mem_range.mp hm)]
    ring

noncomputable def pair (u : ℕ → ℂ) (c : ℕ) : Polynomial ℂ →ₗ[ℂ] ℂ :=
  Polynomial.lsum fun j =>
    { toFun := fun a => a * u (j + c)
      map_add' := by intros; ring
      map_smul' := by intros; simp [mul_assoc] }

theorem pair_monomial (u : ℕ → ℂ) (c k : ℕ) (a : ℂ) :
    pair u c (C a * X ^ k) = a * u (k + c) := by
  rw [C_mul_X_pow_eq_monomial]
  change (monomial k a).sum (fun j b => b * u (j + c)) = _
  simp

theorem pair_scalar (u : ℕ → ℂ) (c : ℕ) (a : ℂ) (f : Polynomial ℂ) :
    pair u c (C a * f) = a * pair u c f := by
  rw [C_mul']
  exact (pair u c).map_smul a f

private theorem annihilation (p q : ℂ) (u : ℕ → ℂ)
    (hu : ∀ n : ℕ, u (n + 2) = p * u (n + 1) + q * u n)
    (c : ℕ) (f : Polynomial ℂ) :
    pair u c ((X ^ 2 - C p * X - C q) * f) = 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [mul_add, map_add, hf, hg, add_zero]
  | monomial k a =>
      rw [← C_mul_X_pow_eq_monomial]
      have expand : (X ^ 2 - C p * X - C q) * (C a * X ^ k) =
          C a * X ^ (k + 2) - C (p * a) * X ^ (k + 1) - C (q * a) * X ^ k := by
        simp only [pow_add, pow_one, C_mul]
        ring
      rw [expand, map_sub, map_sub, pair_monomial, pair_monomial, pair_monomial]
      have h := hu (k + c)
      have e₂ : k + 2 + c = k + c + 2 := by omega
      have e₁ : k + 1 + c = k + c + 1 := by omega
      rw [e₂, e₁, h]
      ring

/-- The all-parameter consequence of the classical geometric-polynomial reflection.
The recurrence alone constrains the sequence, leaving both initial values arbitrary. -/
theorem result (p q : ℂ) (ell c : ℕ) (u : ℕ → ℂ)
    (hu : ∀ n : ℕ, u (n + 2) = p * u (n + 1) + q * u n) :
    (∑ m ∈ range (ell + 1),
      (-1 : ℂ) ^ m *
        ((Nat.factorial m * Nat.stirlingSecond (ell + 1) (m + 1) : ℕ) : ℂ) *
        q ^ (ell - m) * u (2 * m + c)) =
    (-1 : ℂ) ^ ell * ∑ m ∈ range (ell + 1),
      ((Nat.factorial m * Nat.stirlingSecond ell m : ℕ) : ℂ) *
        p ^ m * q ^ (ell - m) * u (m + c) := by
  let A : Polynomial ℂ := C q + C p * X
  have power_pair (m : ℕ) : pair u c (A ^ m) = u (2 * m + c) := by
    have hdiv : (X ^ 2 - C p * X - C q : Polynomial ℂ) ∣ (X ^ 2) ^ m - A ^ m := by
      have h := sub_dvd_pow_sub_pow (X ^ 2 : Polynomial ℂ) A m
      have hf : (X ^ 2 : Polynomial ℂ) - A = X ^ 2 - C p * X - C q := by
        dsimp [A]; ring
      rwa [hf] at h
    obtain ⟨f, hf⟩ := hdiv
    have hz := annihilation p q u hu c f
    rw [← hf, map_sub] at hz
    have he : pair u c ((X ^ 2) ^ m) = u (2 * m + c) := by
      rw [← pow_mul]
      simpa using pair_monomial u c (2 * m) 1
    rw [he] at hz
    exact (sub_eq_zero.mp hz).symm
  have poly := congrArg
    (MvPolynomial.eval₂Hom (C.comp (Int.castRingHom ℂ)) ![C p * X, C q])
    (homogeneous_reflection ell)
  simp only [map_sum, map_mul, map_pow, map_sub, map_neg,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Int.coe_castRingHom, Int.cast_natCast,
    Int.cast_one] at poly
  simp only [← C_pow, ← C_neg] at poly
  have hn : (C (-q) - C p * X : Polynomial ℂ) = -A := by
    rw [C_neg]; dsimp [A]; ring
  simp only [hn] at poly
  have lp (m : ℕ) (d : ℂ) :
      pair u c (C d * (-A) ^ m * C (q ^ (ell - m))) =
        (-1 : ℂ) ^ m * d * q ^ (ell - m) * u (2 * m + c) := by
    have hp : C d * (-A) ^ m * C (q ^ (ell - m)) =
        C ((-1 : ℂ) ^ m * d * q ^ (ell - m)) * A ^ m := by
      rw [neg_pow]
      simp only [C_mul, C_pow, C_neg, C_1]
      ring
    rw [hp, pair_scalar, power_pair]
  have rp (m : ℕ) (d : ℂ) :
      pair u c (C d * (C p * X) ^ m * C (q ^ (ell - m))) =
        d * p ^ m * q ^ (ell - m) * u (m + c) := by
    have hp : C d * (C p * X) ^ m * C (q ^ (ell - m)) =
        C (d * p ^ m * q ^ (ell - m)) * X ^ m := by
      simp only [mul_pow, C_mul, C_pow]
      ring
    rw [hp, pair_monomial]
  have paired := congrArg (pair u c) poly
  simpa only [map_sum, pair_scalar, lp, rp] using paired

end D5.S3.Combinatorics.BinomialBases.SecondOrderStirlingTransform
