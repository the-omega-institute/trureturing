/- GID: D5/S3/Quantum/Petz/DensityPositivity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict positivity of the Stieltjes density at distinct and confluent positive nodes. -/

import D5.S3.Quantum.Petz.StieltjesDensity
import D5.S3.Quantum.PositiveResolvent.LogisticDensityBounds

namespace D5.S3.Quantum.Petz.DensityPositivity

open D5.S3.Quantum.Petz.StieltjesDensity
open D5.S3.Quantum.PositiveResolvent

private lemma rho_log_form {y z t : ℝ} (hy : 0 < y) (hz : 0 < z) (ht : 0 < t)
    (hne : y ≠ z) :
    let a := Real.log (t / y)
    let b := Real.log (t / z)
    rho y z t = (ell a)⁻¹ * (ell b)⁻¹ / (6 * t) *
      (2 * (ell a - ell b) / (b - a) -
        (jfun b - jfun a) / (Real.exp b - Real.exp a)) := by
  dsimp
  have hexp (r : ℝ) : Real.exp (2 * r) = (Real.exp r) ^ 2 := by
    rw [show 2 * r = r + r by ring, Real.exp_add, pow_two]
  have hea := Real.exp_log (div_pos ht hy)
  have heb := Real.exp_log (div_pos ht hz)
  have hlog : Real.log (t / z) - Real.log (t / y) = Real.log (y / z) := by
    rw [Real.log_div ht.ne' hz.ne', Real.log_div ht.ne' hy.ne',
      Real.log_div hy.ne' hz.ne']
    ring
  have hln : Real.log (y / z) ≠ 0 := by
    rw [Real.log_div hy.ne' hz.ne']
    exact sub_ne_zero.mpr (fun h => hne (Real.log_injOn_pos hy hz h))
  have hD (u : ℝ) : (Real.log (t / u)) ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
  simp only [rho, if_neg hne, ell, jfun, hexp, hea, heb, hlog]
  dsimp [rP, rQ]
  field_simp [hy.ne', hz.ne', ht.ne', (add_pos ht hy).ne',
    (add_pos ht hz).ne', hD y, hD z, sub_ne_zero.mpr hne, hln]
  <;> ring

private lemma rho_confluent_log_form {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    let a := Real.log (t / y)
    rho y y t = (ell a)⁻¹ ^ 2 / (6 * t) *
      (2 * (-deriv ell a) - Real.exp (-a) * deriv jfun a) := by
  dsimp
  have hexp (r : ℝ) : Real.exp (2 * r) = (Real.exp r) ^ 2 := by
    rw [show 2 * r = r + r by ring, Real.exp_add, pow_two]
  rw [ell_deriv_formula, jfun_deriv_formula, Real.exp_neg, hexp,
    Real.exp_log (div_pos ht hy)]
  rw [rho, if_pos rfl]
  simp only [ell, Real.exp_log (div_pos ht hy)]
  have hD : (Real.log (t / y)) ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
  field_simp [hy.ne', ht.ne', (add_pos ht hy).ne', hD]
  <;> ring

/-- The boundary density is strictly positive, including its confluent branch. -/
theorem rho_pos {y z t : ℝ} (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) :
    0 < rho y z t := by
  have he (a : ℝ) : 0 < ell a := by unfold ell; positivity
  have hi (a : ℝ) : 0 < (ell a)⁻¹ := inv_pos.mpr (he a)
  by_cases hne : y = z
  · subst z
    rw [rho_confluent_log_form hy ht]
    exact mul_pos (div_pos (sq_pos_of_pos (hi _)) (by positivity))
      (density_bracket_pos_confluent _)
  · rw [rho_log_form hy hz ht hne]
    apply mul_pos (div_pos (mul_pos (hi _) (hi _)) (by positivity))
    let a := Real.log (t / y)
    let b := Real.log (t / z)
    have hab : a ≠ b := by
      intro h
      have heq := congrArg Real.exp h
      dsimp [a, b] at heq
      rw [Real.exp_log (div_pos ht hy), Real.exp_log (div_pos ht hz)] at heq
      exact hne (mul_left_cancel₀ ht.ne'
        ((div_eq_div_iff hy.ne' hz.ne').mp heq).symm)
    rcases lt_or_gt_of_ne hab with h | h
    · exact sub_pos.mpr (density_bracket_pos h)
    · have hb := density_bracket_pos h
      have hl : (ell b - ell a) / (a - b) = (ell a - ell b) / (b - a) := by
        rw [show ell b - ell a = -(ell a - ell b) by ring,
          show a - b = -(b - a) by ring, neg_div_neg_eq]
      have hj : (jfun a - jfun b) / (Real.exp a - Real.exp b) =
          (jfun b - jfun a) / (Real.exp b - Real.exp a) := by
        rw [show jfun a - jfun b = -(jfun b - jfun a) by ring,
          show Real.exp a - Real.exp b = -(Real.exp b - Real.exp a) by ring,
          neg_div_neg_eq]
      rw [hj, mul_div_assoc, hl, ← mul_div_assoc] at hb
      exact sub_pos.mpr hb

end D5.S3.Quantum.Petz.DensityPositivity
