/- GID: D5/S3/Analytic/RealRootedCoefficientNewton
   generality: G
   mirror-B: D5/B/S3/Analytic/RealRootedCoefficientNewton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Polynomial, mathlib/module/Mathlib.Algebra.Polynomial.Splits]
   utility: none
   digest: Real splitting implies strong coefficient Newton inequalities through derivative closure and Laguerre positivity. -/

import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.RealRootedCoefficientNewton

open Polynomial

/-- Strong coefficient Newton inequalities for every real split polynomial. -/
theorem split_polynomial_coefficient_newton (p : ℝ[X]) (hp : p.Splits) (k : ℕ) :
    (k + 1 : ℝ) * p.coeff (k + 1) ^ 2 ≥
      (k + 2 : ℝ) * p.coeff k * p.coeff (k + 2) := by
  have hder (q : ℝ[X]) (hq : q.Splits) : q.derivative.Splits := by
    rw [splits_iff_card_roots] at hq ⊢
    have hr := q.card_roots_le_derivative
    have hu := q.derivative.card_roots'
    rw [hq] at hr
    rw [natDegree_derivative] at hu ⊢
    omega
  have hlag (q : ℝ[X]) (hq : q.Splits) (x : ℝ) :
      0 ≤ q.derivative.eval x ^ 2 - q.eval x * q.derivative.derivative.eval x := by
    induction hq using Submonoid.closure_induction with
    | mem q hq =>
        rcases hq with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> simp
    | one => simp
    | mul f g hf hg ihf ihg =>
        simp only [derivative_mul, derivative_add, eval_add, eval_mul]
        nlinarith only [mul_nonneg (sq_nonneg (g.eval x)) ihf,
          mul_nonneg (sq_nonneg (f.eval x)) ihg]
  induction k generalizing p with
  | zero =>
      have h := hlag p hp 0
      simp only [← coeff_zero_eq_eval_zero, coeff_derivative] at h
      norm_num at h ⊢
      nlinarith only [h]
  | succ k ih =>
      have h := ih p.derivative (hder p hp)
      simp only [coeff_derivative] at h
      push_cast at h ⊢
      have hc : 0 < (k + 1 : ℝ) * (k + 2) := by positivity
      nlinarith only [h, hc]

#print axioms split_polynomial_coefficient_newton

end D5.S3.Analytic.RealRootedCoefficientNewton
