/- GID: D5/S3/Observer/Residuals/GoldenResidualPeriodicity
   generality: G
   mirror-B: D5/B/S3/Observer/Residuals/GoldenResidualPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The unforced golden residual map has only zero as a fixed or finite-period point. -/

import Mathlib.NumberTheory.Real.GoldenRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Residuals.GoldenResidualPeriodicity

/- Library-search audit trail (2026-08-29):
   * The canonical source scalar is Mathlib's `Real.goldenRatio`; no local alias is introduced.
   * Exact supporting hits are `Real.inv_goldenRatio`, `Real.goldenRatio_add_goldenConj`,
     `Real.goldenRatio_pos`, `Real.one_lt_goldenRatio`, and `pow_lt_one₀`.
   * Repository and pinned-Mathlib searches found no theorem stating both the fixed-point and
     every-positive-period clauses for this explicit residual map. -/

/-- Multiplication by the negative reciprocal golden ratio has exactly one fixed point, zero,
and zero is also the only point fixed by any positive iterate. -/
theorem unforced_golden_completion_has_no_off_line_fixed_point :
    (forall delta : Real,
      -Real.goldenRatio⁻¹ * delta = delta <-> delta = 0) /\
    (forall k : Nat, 0 < k -> forall delta : Real,
      ((fun x : Real => -Real.goldenRatio⁻¹ * x)^[k]) delta = delta <->
        delta = 0) := by
  have scale_identity : 1 + Real.goldenRatio⁻¹ = Real.goldenRatio := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have base_abs_lt_one : |-Real.goldenRatio⁻¹| < (1 : Real) := by
    rw [abs_neg, abs_inv, abs_of_pos Real.goldenRatio_pos]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have iterate_formula : forall (k : Nat) (delta : Real),
      ((fun x : Real => -Real.goldenRatio⁻¹ * x)^[k]) delta =
        (-Real.goldenRatio⁻¹) ^ k * delta := by
    intro k
    induction k with
    | zero => intro delta; simp
    | succ k inductionHypothesis =>
        intro delta
        rw [Function.iterate_succ_apply', inductionHypothesis]
        ring
  constructor
  · intro delta
    constructor
    · intro fixed
      have zero_product : (1 + Real.goldenRatio⁻¹) * delta = 0 := by
        calc
          (1 + Real.goldenRatio⁻¹) * delta =
              delta + Real.goldenRatio⁻¹ * delta := by ring
          _ = 0 := by nlinarith [fixed]
      rw [scale_identity] at zero_product
      exact (mul_eq_zero.mp zero_product).resolve_left Real.goldenRatio_ne_zero
    · rintro rfl
      ring
  · intro k positivePeriod delta
    constructor
    · intro periodic
      rw [iterate_formula] at periodic
      have coefficient_abs_lt_one : |(-Real.goldenRatio⁻¹) ^ k| < (1 : Real) := by
        rw [abs_pow]
        exact pow_lt_one₀ (abs_nonneg _) base_abs_lt_one
          (Nat.ne_of_gt positivePeriod)
      have coefficient_ne_one : Not ((-Real.goldenRatio⁻¹) ^ k = (1 : Real)) := by
        intro coefficient_eq
        rw [coefficient_eq, abs_one] at coefficient_abs_lt_one
        exact (lt_irrefl 1 coefficient_abs_lt_one)
      have zero_product : (((-Real.goldenRatio⁻¹) ^ k) - 1) * delta = 0 := by
        nlinarith [periodic]
      rcases mul_eq_zero.mp zero_product with coefficient_zero | delta_zero
      · exact (coefficient_ne_one (sub_eq_zero.mp coefficient_zero)).elim
      · exact delta_zero
    · rintro rfl
      rw [iterate_formula]
      ring

#print axioms unforced_golden_completion_has_no_off_line_fixed_point

end D5.S3.Observer.Residuals.GoldenResidualPeriodicity
