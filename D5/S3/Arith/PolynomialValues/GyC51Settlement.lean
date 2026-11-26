/- GID: D5/S3/Arith/PolynomialValues/GyC51Settlement
   generality: I
   mirror-B: D5/B/S3/Arith/PolynomialValues/GyC51Settlement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: An affine common-factor family refutes Gy's coefficient log-concavity question. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import D5.S0.Certificates.GiacomelliLogConcaveConeNonconvex
import D5.S1.Phase.Interference.DedekindReciprocityFiniteSums

set_option autoImplicit false

namespace D5.S3.Arith.PolynomialValues.GyC51Settlement

open D5.S0.Certificates.GiacomelliLogConcaveConeNonconvex (logConcaveOp)

/-- The prefix consisting of the source's variables x₁ through xₘ. -/
def inputPrefix (x : ℕ → Polynomial ℝ) (m : ℕ) (i : Fin m) : Polynomial ℝ :=
  x (i.val + 1)

/-- Gy's coefficientwise polynomial order, printed page 15. -/
def qLe (f g : Polynomial ℝ) : Prop :=
  ∀ k : ℕ, 0 ≤ (g - f).coeff k

/-- The left index in the source inequality is i + 1, so its predecessor is i. -/
def StronglyQLogConcave (x : ℕ → Polynomial ℝ) : Prop :=
  ∀ i r : ℕ, i ≤ r → qLe (x i * x (r + 1)) (x (i + 1) * x r)

/-- The elementary symmetric polynomial evaluated on the first m terms. -/
noncomputable def e (x : ℕ → Polynomial ℝ) (m d : ℕ) : Polynomial ℝ :=
  MvPolynomial.eval (inputPrefix x m) (MvPolynomial.esymm (Fin m) (Polynomial ℝ) d)

/-- The complete homogeneous symmetric polynomial evaluated on the first m terms. -/
noncomputable def h (x : ℕ → Polynomial ℝ) (m d : ℕ) : Polynomial ℝ :=
  MvPolynomial.eval (inputPrefix x m) (MvPolynomial.hsymm (Fin m) (Polynomial ℝ) d)

/-- The elementary triple-product difference in Conjecture 5.1. -/
noncomputable def E (x : ℕ → Polynomial ℝ) (n p j : ℕ) : Polynomial ℝ :=
  e x n (n - p) * e x p (p - j) * e x (n - 1) (n - j) -
    e x (n - 1) (n - p) * e x (p - 1) (p - j) * e x n (n - j)

/-- The complete homogeneous triple-product difference in Conjecture 5.1. -/
noncomputable def H (x : ℕ → Polynomial ℝ) (n p j : ℕ) : Polynomial ℝ :=
  h x p (n - p) * h x j (p - j) * h x (j + 1) (n - j) -
    h x (p + 1) (n - p) * h x (j + 1) (p - j) * h x j (n - j)

/-- The coefficient sequence through the degree satisfies Gy's adjacent inequalities. -/
def CoeffLogConcave (f : Polynomial ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < f.natDegree → 0 ≤ logConcaveOp f.coeff k

/-- The unnumbered general coefficient question in Section 5, printed page 16. -/
def claim : Prop :=
  ∀ x : ℕ → Polynomial ℝ, StronglyQLogConcave x →
    ∀ n p j : ℕ, 1 ≤ j → j ≤ p → p ≤ n →
      CoeffLogConcave (E x n p j) ∧ CoeffLogConcave (H x n p j)


open Polynomial
open D5.S1.Phase.Interference.DedekindReciprocityFiniteSums (sum_Ico_cast sum_Ico_cast_sq)
open scoped BigOperators

private noncomputable def prefixSum (x : ℕ → Polynomial ℝ) (m : ℕ) : Polynomial ℝ :=
  ∑ i : Fin m, inputPrefix x m i

private noncomputable def prefixSquares (x : ℕ → Polynomial ℝ) (m : ℕ) : Polynomial ℝ :=
  ∑ i : Fin m, inputPrefix x m i ^ 2

private theorem e_one (x : ℕ → Polynomial ℝ) (m : ℕ) : e x m 1 = prefixSum x m := by
  simp [e, prefixSum]

private theorem e_two (x : ℕ → Polynomial ℝ) (m : ℕ) :
    2 * e x m 2 = prefixSum x m ^ 2 - prefixSquares x m := by
  have hn := MvPolynomial.mul_esymm_eq_sum (Fin m) (Polynomial ℝ) 2
  have pairs : (Finset.antidiagonal (2 : ℕ)).filter (fun a => a.1 < 2) = {(0, 2), (1, 1)} := by
    decide
  rw [pairs] at hn
  have he := congrArg (MvPolynomial.eval (inputPrefix x m)) hn
  simp [Finset.sum_insert, MvPolynomial.psum, MvPolynomial.esymm_one] at he
  unfold e prefixSum prefixSquares
  linear_combination he

private noncomputable def quadratic (t : ℝ) : Polynomial ℝ := 1 + X + monomial 2 t

private noncomputable def affineInput (a t : ℝ) (k : ℕ) : Polynomial ℝ :=
  C ((k : ℝ) + a) * quadratic t

private noncomputable def affineSum (a : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * ((m : ℝ) + 1 + 2 * a) / 2

private noncomputable def affineSquares (a : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / 6 +
    a * (m : ℝ) * ((m : ℝ) + 1) + (m : ℝ) * a ^ 2

private theorem sum_affine (a : ℝ) (m : ℕ) :
    (∑ i : Fin m, (((i.val + 1 : ℕ) : ℝ) + a)) = affineSum a m := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (sum_Ico_cast (m + 1))
  rw [Finset.sum_Ico_eq_sum_range] at h
  push_cast at h
  simp only [add_comm (1 : ℝ)] at h
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (((i + 1 : ℕ) : ℝ) + a)) m]
  push_cast
  rw [Finset.sum_add_distrib, h]
  simp [affineSum]
  ring

private theorem sum_affine_squares (a : ℝ) (m : ℕ) :
    (∑ i : Fin m, (((i.val + 1 : ℕ) : ℝ) + a) ^ 2) = affineSquares a m := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (sum_Ico_cast_sq (m + 1))
  rw [Finset.sum_Ico_eq_sum_range] at h
  push_cast at h
  simp only [Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, add_comm (1 : ℝ)] at h
  have hBase := sum_affine 0 m
  simp only [add_zero] at hBase
  calc
    _ = ∑ i : Fin m, (((i.val + 1 : ℕ) : ℝ) ^ 2 +
          2 * a * ((i.val + 1 : ℕ) : ℝ) + a ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hBase,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ 2) m]
      push_cast
      rw [h]
      unfold affineSum affineSquares
      ring

private theorem prefixSum_affine (a t : ℝ) (m : ℕ) :
    prefixSum (affineInput a t) m = C (affineSum a m) * quadratic t := by
  simp only [prefixSum, inputPrefix, affineInput, ← Finset.sum_mul, ← map_sum, sum_affine]

private theorem prefixSquares_affine (a t : ℝ) (m : ℕ) :
    prefixSquares (affineInput a t) m = C (affineSquares a m) * quadratic t ^ 2 := by
  simp only [prefixSquares, inputPrefix, affineInput, mul_pow, ← map_pow, ← Finset.sum_mul,
    ← map_sum, sum_affine_squares]

private theorem e_two_affine (a t : ℝ) (m : ℕ) :
    e (affineInput a t) m 2 =
      C ((affineSum a m ^ 2 - affineSquares a m) / 2) * quadratic t ^ 2 := by
  apply mul_left_cancel₀ (show (2 : Polynomial ℝ) ≠ 0 by norm_num)
  rw [e_two, prefixSum_affine, prefixSquares_affine, mul_pow, ← map_pow, ← sub_mul, ← map_sub,
    ← mul_assoc, ← C_ofNat 2, ← map_mul]
  congr 1
  congr 1
  ring

private noncomputable def familyScale (a : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) * ((j : ℝ) + 1) ^ 2 * ((j : ℝ) + 2) *
    (2 * a + (j : ℝ) + 2) * (4 * a + (j : ℝ) + 3) / 48

private theorem affine_elementary_difference (a t : ℝ) (j : ℕ) :
    E (affineInput a t) (j + 2) (j + 1) j = C (familyScale a j) * quadratic t ^ 4 := by
  have step : j + 2 - (j + 1) = 1 := by omega
  have pred : j + 2 - 1 = j + 1 := by omega
  simp only [E, step, pred, Nat.add_sub_cancel_left, Nat.add_sub_cancel, e_one,
    prefixSum_affine, e_two_affine]
  calc
    _ = (C (affineSum a (j + 2)) * C (affineSum a (j + 1)) *
        C ((affineSum a (j + 1) ^ 2 - affineSquares a (j + 1)) / 2) -
        C (affineSum a (j + 1)) * C (affineSum a j) *
        C ((affineSum a (j + 2) ^ 2 - affineSquares a (j + 2)) / 2)) *
        quadratic t ^ 4 := by ring
    _ = _ := by
      simp only [← map_mul, ← map_sub]
      congr 1
      congr 1
      push_cast [affineSum, affineSquares, familyScale]
      ring

private theorem affine_gap (a t : ℝ) (i r : ℕ) :
    affineInput a t (i + 1) * affineInput a t r -
      affineInput a t i * affineInput a t (r + 1) =
      C ((r : ℝ) - (i : ℝ)) * quadratic t ^ 2 := by
  calc
    _ = (C (((i + 1 : ℕ) : ℝ) + a) * C ((r : ℝ) + a) -
        C ((i : ℝ) + a) * C (((r + 1 : ℕ) : ℝ) + a)) * quadratic t ^ 2 := by
      unfold affineInput
      ring
    _ = _ := by
      simp only [← map_mul, ← map_sub, Nat.cast_succ]
      congr 1
      congr 1
      ring

private theorem affine_strong (a t : ℝ) (ht : 0 ≤ t) :
    StronglyQLogConcave (affineInput a t) := by
  intro i r hir k
  rw [affine_gap, coeff_C_mul, pow_two, coeff_mul]
  refine mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hir)) (Finset.sum_nonneg ?_)
  have hcoeff (k : ℕ) : 0 ≤ (quadratic t).coeff k := by
    simp only [quadratic, coeff_add, coeff_one, coeff_X, coeff_monomial]
    split_ifs <;> positivity
  exact fun v _ => mul_nonneg (hcoeff v.1) (hcoeff v.2)

private theorem quadratic_four_coeffs (t : ℝ) :
    (quadratic t ^ 4).coeff 0 = 1 ∧
    (quadratic t ^ 4).coeff 1 = 4 ∧
    (quadratic t ^ 4).coeff 2 = 6 + 4 * t := by
  have c0 : (quadratic t).coeff 0 = 1 := by norm_num [quadratic, coeff_monomial, coeff_one]
  have c1 : (quadratic t).coeff 1 = 1 := by norm_num [quadratic, coeff_monomial, coeff_one]
  have c2 : (quadratic t).coeff 2 = t := by norm_num [quadratic, coeff_monomial, coeff_one, coeff_X]
  have ad1 : Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
  have ad2 : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by decide
  have p4 : quadratic t ^ 4 = (quadratic t * quadratic t) * (quadratic t * quadratic t) := by ring
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [p4, coeff_mul, ad1, ad2, Finset.sum_insert, c0, c1, c2]
  ring

private theorem scaled_four_failure (c t : ℝ) (hc : 0 < c) (ht : 5 / 2 < t) :
    ¬ CoeffLogConcave (C c * quadratic t ^ 4) := by
  let f : Polynomial ℝ := C c * quadratic t ^ 4
  have ht0 : 0 < t := by linarith
  obtain ⟨q0, q1, q2⟩ := quadratic_four_coeffs t
  have c0 : f.coeff 0 = c := by simp [f, q0]
  have c1 : f.coeff 1 = 4 * c := by simp [f, q1, mul_comm]
  have c2 : f.coeff 2 = c * (6 + 4 * t) := by simp [f, coeff_C_mul, q2]
  have interior : 1 < f.natDegree :=
    lt_of_lt_of_le (by decide : 1 < 2) (le_natDegree_of_ne_zero (by rw [c2]; positivity))
  have determinant : logConcaveOp f.coeff 1 = (10 - 4 * t) * c ^ 2 := by
    norm_num [logConcaveOp, c0, c1, c2]
    ring
  have negative : logConcaveOp f.coeff 1 < 0 := by
    rw [determinant]
    exact mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hc)
  exact fun hf => (not_le_of_gt negative) (hf 1 (by decide) interior)

private theorem familyScale_pos (a : ℝ) (j : ℕ) (ha : 0 < a) (hj : 1 ≤ j) :
    0 < familyScale a j := by
  have hj' : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  unfold familyScale
  positivity

private theorem affine_elementary_failure (a t : ℝ) (j : ℕ)
    (ha : 0 < a) (ht : 5 / 2 < t) (hj : 1 ≤ j) :
    ¬ CoeffLogConcave (E (affineInput a t) (j + 2) (j + 1) j) := by
  rw [affine_elementary_difference]
  exact scaled_four_failure (familyScale a j) t (familyScale_pos a j ha hj) ht

theorem result : ¬ claim := by
  intro assertion
  have strong := affine_strong 1 3 (by norm_num)
  have eFails := affine_elementary_failure 1 3 1 (by norm_num) (by norm_num) (by decide)
  exact eFails (assertion (affineInput 1 3) strong 3 2 1 (by decide) (by decide) (by decide)).1

end D5.S3.Arith.PolynomialValues.GyC51Settlement
