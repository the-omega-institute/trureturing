/- GID: D5/S3/Zeros/Jensen/WeakQlpDifferentiation
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/WeakQlpDifferentiation
   mirror-E: none(waiver:exact-polynomial-identities)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/Jensen/WeakQlpDifferentiation.Question62Claim; result=D5/S3/Zeros/Jensen/WeakQlpDifferentiation.question62_refuted; claim=D5/S3/Zeros/Jensen/WeakQlpDifferentiation.Question62Claim
   digest: A rational cubic refutes differentiation closure of the weak q-Laguerre-Polya class. -/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace D5.S3.Zeros.Jensen.WeakQlpDifferentiation

noncomputable section
open Polynomial

/-- The normalized q-Borel transform on real polynomials. For an ordinary
coefficient `c_k`, the exponential coefficient is `a_k = k! * c_k`, so the
factorial below is essential. The denominator is `(q;q)_k`. This is equation
(1.6), p. 3, of Dimitrov--Shapiro, arXiv:2606.17864v1, using (1.3), p. 2.
Only `0 < q < 1` is used in the closure claim; outside this interval the
definition uses Lean's total division. -/
def qBorel (q : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum fun k => (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight
    (monomial k ((Nat.factorial k : ℝ) * q ^ (k * (k - 1) / 2) *
      (1 - q) ^ k / ∏ j ∈ Finset.range k, (1 - q ^ (j + 1))))

/-- The ordinary coefficients of the counterexample at `q = 1/2`. -/
def halfCounterexample : ℝ[X] :=
  monomial 0 1 + monomial 1 3 + monomial 2 (9 / 2) + monomial 3 (7 / 2)

-- Anonymous normalization self-test; the sole named theorem will be the refutation.
example : qBorel (1 / 2) halfCounterexample = (X + 1) ^ 3 := by
  norm_num [qBorel, halfCounterexample, Polynomial.lsum_apply, Polynomial.sum_add_index,
    Polynomial.sum_monomial_index, add_smul, Nat.factorial, Finset.prod_range_succ]
  norm_num [Polynomial.sum, show (1 : ℝ[X]).support = {0} by
    simpa only [C_1] using support_C (one_ne_zero : (1 : ℝ) ≠ 0),
    smul_monomial, smul_eq_mul]
  norm_num [← C_mul_X_pow_eq_monomial, smul_eq_C_mul, map_ofNat]
  ring

/-- The polynomial restriction of Question 6.2, p. 12, of
arXiv:2606.17864v1. Definition 1.1, p. 3, makes the weak class the inverse
image of the classical Laguerre--Polya class under `qBorel`.

For real polynomials, membership in the classical class is equivalent to
splitting over the reals: one direction uses a constant approximating
sequence, and the other follows from Hurwitz's theorem. `Polynomial.Splits`
also includes zero. Thus closure for the paper's entire-function class
(defined using locally uniform limits) would imply this polynomial claim.
The analytic equivalence is the interpretation of this restriction; it is
not an additional Lean theorem asserted by this module. -/
def Question62Claim : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → ∀ f : ℝ[X],
    (qBorel q f).Splits → (qBorel q f.derivative).Splits

/-- At `q = 1/2`, the witness maps to `(X + 1)^3`, but its derivative maps
to `7 * X^2 + 9 * X + 3`. The latter has discriminant `-3`, hence no real
root, so it cannot split. This refutes the polynomial restriction and
therefore differentiation closure of the entire-function class. -/
theorem question62_refuted : ¬ Question62Claim := by
  intro h
  have hB : qBorel (1 / 2) halfCounterexample = (X + 1) ^ 3 := by
    norm_num [qBorel, halfCounterexample, Polynomial.lsum_apply, Polynomial.sum_add_index,
      Polynomial.sum_monomial_index, add_smul, Nat.factorial, Finset.prod_range_succ]
    norm_num [Polynomial.sum, show (1 : ℝ[X]).support = {0} by
      simpa only [C_1] using support_C (one_ne_zero : (1 : ℝ) ≠ 0),
      smul_monomial, smul_eq_mul]
    norm_num [← C_mul_X_pow_eq_monomial, smul_eq_C_mul, map_ofNat]
    ring
  have hD : qBorel (1 / 2) halfCounterexample.derivative =
      C 7 * X ^ 2 + C 9 * X + C 3 := by
    norm_num [qBorel, halfCounterexample, Polynomial.lsum_apply, derivative_add,
      derivative_monomial, Polynomial.sum_add_index, Polynomial.sum_monomial_index,
      add_smul, Nat.factorial, Finset.prod_range_succ]
    norm_num [smul_monomial, smul_eq_mul]
    norm_num [← C_mul_X_pow_eq_monomial, smul_eq_C_mul, map_ofNat]
    ring
  have hf : (qBorel (1 / 2) halfCounterexample).Splits := by
    rw [hB]
    simpa only [C_1] using (Splits.X_add_C (1 : ℝ)).pow 3
  have hd : (qBorel (1 / 2) halfCounterexample.derivative).Splits :=
    h (1 / 2) (by norm_num) (by norm_num) halfCounterexample hf
  rw [hD] at hd
  obtain ⟨x, hx⟩ := hd.exists_eval_eq_zero (by
    rw [degree_quadratic (by norm_num : (7 : ℝ) ≠ 0)]
    norm_num)
  have hx' : (7 : ℝ) * (x * x) + 9 * x + 3 = 0 := by
    simpa only [eval_add, eval_mul, eval_C, eval_pow, eval_X, pow_two] using hx
  have hs := discrim_eq_sq_of_quadratic_eq_zero hx'
  norm_num [discrim] at hs
  have hn := sq_nonneg (2 * (7 : ℝ) * x + 9)
  linarith only [hs, hn]

#print axioms qBorel
#print axioms halfCounterexample
#print axioms Question62Claim
#print axioms question62_refuted

end
end D5.S3.Zeros.Jensen.WeakQlpDifferentiation
