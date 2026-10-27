/- Uncompiled source fragment for the complete original theta modes.
   The estimate keeps the absolute polynomial at the actual mode scale,
   without the larger Gaussian-endpoint constant. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.OriginalPrimalTailProjection

noncomputable section

namespace RhTransient.PrimalJetSharpEndpoint

open Real Polynomial
open D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private jet_degree from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection

/-- The coefficientwise absolute polynomial, at the literal integer-mode scale. -/
def absoluteJetPolynomial (r : ℕ) (A : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (r + 3), |(jetPolynomial r).coeff k| * A ^ k

private theorem monomial_endpoint {A σ x : ℝ} (k : ℕ)
    (hx : 0 ≤ x) (hσ : 0 ≤ σ)
    (hA : (k : ℝ) + 1 / 4 + σ / 2 ≤ A) :
    exp (x / 2) * exp (-A * exp (2 * x)) * (A * exp (2 * x)) ^ k ≤
      exp (-A) * A ^ k * exp (-σ * x) := by
  have hA0 : 0 ≤ A := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hscale := mul_le_mul_of_nonneg_left (add_one_le_exp (2 * x)) hA0
  have hgap := mul_nonneg (sub_nonneg.mpr hA) hx
  have hexponent :
      x / 2 + -A * exp (2 * x) + (k : ℝ) * (2 * x) ≤ -A + -σ * x := by
    nlinarith
  calc
    _ = A ^ k * exp (x / 2 + -A * exp (2 * x) + (k : ℝ) * (2 * x)) := by
      rw [mul_pow, ← exp_nat_mul, exp_add, exp_add]
      ring
    _ ≤ A ^ k * exp (-A + -σ * x) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexponent) (pow_nonneg hA0 k)
    _ = _ := by rw [exp_add]; ring

/-- A sharp exponential envelope for every derivative of every actual mode.
    The entire degree range of the derivative polynomial is retained. -/
theorem primalJet_sharp_endpoint {r m : ℕ} {σ x : ℝ}
    (hx : 0 ≤ x) (hσ : 0 ≤ σ)
    (hA : (r : ℝ) + 9 / 4 + σ / 2 ≤ modeScale m) :
    |primalJet r m x| ≤
      exp (-modeScale m) * absoluteJetPolynomial r (modeScale m) * exp (-σ * x) := by
  let A := modeScale m
  let y := A * exp (2 * x)
  let e := exp (x / 2) * exp (-A * exp (2 * x))
  have hA0 : 0 ≤ A := by dsimp [A, modeScale]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hdegree : (jetPolynomial r).natDegree < r + 3 := by
    have := jet_degree r
    omega
  have hpoly : |(jetPolynomial r).eval y| ≤
      ∑ k ∈ Finset.range (r + 3), |(jetPolynomial r).coeff k| * y ^ k := by
    rw [eval_eq_sum_range' hdegree]
    apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
    apply Finset.sum_congr rfl
    intro k hk
    rw [abs_mul, abs_of_nonneg (pow_nonneg hy k)]
  calc
    |primalJet r m x| = e * |(jetPolynomial r).eval y| := by
      simp only [primalJet, e, y, A, abs_mul, abs_of_pos (exp_pos _)]
    _ ≤ e * (∑ k ∈ Finset.range (r + 3),
        |(jetPolynomial r).coeff k| * y ^ k) :=
      mul_le_mul_of_nonneg_left hpoly he
    _ = ∑ k ∈ Finset.range (r + 3),
        |(jetPolynomial r).coeff k| * (e * y ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∑ k ∈ Finset.range (r + 3),
        |(jetPolynomial r).coeff k| * (exp (-A) * A ^ k * exp (-σ * x)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkr : (k : ℝ) ≤ (r : ℝ) + 2 := by
        exact_mod_cast (show k ≤ r + 2 by
          have := Finset.mem_range.mp hk
          omega)
      have hAk : (k : ℝ) + 1 / 4 + σ / 2 ≤ A := by dsimp [A]; linarith
      exact mul_le_mul_of_nonneg_left
        (monomial_endpoint k hx hσ hAk) (abs_nonneg _)
    _ = _ := by
      simp only [absoluteJetPolynomial, A, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

end RhTransient.PrimalJetSharpEndpoint

#print axioms RhTransient.PrimalJetSharpEndpoint.primalJet_sharp_endpoint
