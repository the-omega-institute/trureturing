/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Taylor, mathlib/module/Mathlib.RingTheory.Polynomial.Chebyshev]
   utility: none
   digest: The auxiliary scalar-weight polynomial is a shifted Chebyshev polynomial. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeScalar
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open scoped BigOperators
open Polynomial

/-- The auxiliary polynomial formed from the scalar weights, not the geometric f-polynomial. -/
noncomputable def crownAuxiliaryPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.Icc 1 n, C (crownScalarWeight n m) * X ^ (m - 1)

/-- The proposed auxiliary identity, with the same rational weights as the
    actual geometric representation. Multiplication by `X` supplies the zero root. -/
theorem crownAuxiliaryPolynomial_chebyshev (n : ℕ) :
    X * crownAuxiliaryPolynomial n =
      2 * ((Chebyshev.T ℚ (n : ℤ)).comp ((X + 2) * C (1 / 2)) - 1) := by
  classical
  -- Consecutive weights satisfy exactly the derivative recurrence at one.
  have hstep (m : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
      2 * (m + 1 : ℚ) * (2 * m + 1) * crownScalarWeight n (m + 1) =
        ((n : ℚ) ^ 2 - (m : ℚ) ^ 2) * crownScalarWeight n m := by
    have ha := Nat.add_one_mul_choose_eq (n + m - 1) (2 * m - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n + m),
      Nat.sub_add_cancel (by omega : 1 ≤ 2 * m)] at ha
    have hb := Nat.choose_succ_right_eq (n + m) (2 * m)
    rw [show n + m - 2 * m = n - m by omega] at hb
    have ha' : ((n : ℚ) + m) * Nat.choose (n + m - 1) (2 * m - 1) =
        (Nat.choose (n + m) (2 * m) : ℚ) * (2 * m) := by exact_mod_cast ha
    have hb' : (Nat.choose (n + m) (2 * m + 1) : ℚ) * (2 * m + 1) =
        (Nat.choose (n + m) (2 * m) : ℚ) * ((n : ℚ) - m) := by
      rw [← Nat.cast_sub (by omega : m ≤ n)]
      exact_mod_cast hb
    unfold crownScalarWeight
    rw [show n + (m + 1) - 1 = n + m by omega,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    push_cast
    have hm0 : (m : ℚ) ≠ 0 := by positivity
    have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    nlinarith [congrArg (fun x : ℚ => n * x) hb',
      congrArg (fun x : ℚ => n * ((n : ℚ) - m) * x) ha']
  let p : Polynomial ℚ := taylor 1 (Chebyshev.T ℚ (n : ℤ))
  have hderiv (k : ℕ) :
      (k.factorial : ℚ) * p.coeff k =
        (derivative^[k] (Chebyshev.T ℚ (n : ℤ))).eval 1 := by
    rw [show p = taylor 1 (Chebyshev.T ℚ (n : ℤ)) from rfl, taylor_coeff]
    have h := congrFun (factorial_smul_hasseDeriv (R := ℚ) (k := k))
      (Chebyshev.T ℚ (n : ℤ))
    simpa [nsmul_eq_mul] using
      congrArg (fun q : Polynomial ℚ => q.eval 1) h
  have hweight (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      2 * p.coeff k = 2 ^ k * crownScalarWeight n k := by
    induction k, hk using Nat.le_induction with
    | base =>
        have hd := hderiv 1
        simp only [Nat.factorial_one, Nat.cast_one, one_mul, Function.iterate_one,
          Chebyshev.derivative_T_eval_one, Int.cast_natCast] at hd
        rw [hd]
        simp [crownScalarWeight, pow_two]
    | succ k hk ih =>
        have ih := ih (by omega)
        have hs := hstep k hk (by omega)
        have hd := Chebyshev.iterate_derivative_T_eval_one_recurrence
          (R := ℚ) (n : ℤ) k
        rw [← hderiv (k + 1), ← hderiv k] at hd
        push_cast at hd
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hd
        have hf : (k.factorial : ℚ) ≠ 0 := by positivity
        have hc : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
        have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
        apply (mul_left_cancel₀ (mul_ne_zero hf (mul_ne_zero hc hk1)))
        rw [pow_succ]
        linear_combination 2 * hd +
          (k.factorial : ℚ) * ((n : ℚ) ^ 2 - (k : ℚ) ^ 2) * ih -
          (k.factorial : ℚ) * 2 ^ k * hs
  have hleft : X * crownAuxiliaryPolynomial n =
      ∑ m ∈ Finset.Icc 1 n, C (crownScalarWeight n m) * X ^ m := by
    unfold crownAuxiliaryPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [show m = (m - 1) + 1 from (Nat.sub_add_cancel hm1).symm] at ⊢
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  have hright : (Chebyshev.T ℚ (n : ℤ)).comp ((X + 2) * C (1 / 2)) =
      p.comp (C (1 / 2) * X) := by
    dsimp only [p]
    rw [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, C_1]
    congr 1
    have hh : C (1 / 2 : ℚ) * 2 = (1 : Polynomial ℚ) := by
      rw [show (2 : Polynomial ℚ) = C (2 : ℚ) by simp only [map_ofNat], ← map_mul]
      norm_num
    linear_combination hh
  rw [hleft, hright]
  ext k
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_ofNat_mul, coeff_sub,
    comp_C_mul_X_coeff, coeff_one]
  rw [Finset.sum_ite_eq]
  by_cases hk0 : k = 0
  · subst k
    simp [p, taylor_coeff_zero, Chebyshev.T_eval_one]
  · have hk : 1 ≤ k := by omega
    rw [if_neg hk0]
    by_cases hkn : k ≤ n
    · rw [if_pos (Finset.mem_Icc.mpr ⟨hk, hkn⟩)]
      have hw := hweight k hk hkn
      have hp : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [one_div_pow]
      field_simp
      nlinarith
    · rw [if_neg (by simpa [Finset.mem_Icc, hk] using hkn)]
      have hd : p.natDegree = n := by simp [p, Chebyshev.natDegree_T]
      rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k)]
      ring

#print axioms crownAuxiliaryPolynomial_chebyshev

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
