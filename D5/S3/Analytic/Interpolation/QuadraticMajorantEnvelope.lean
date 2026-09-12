/- GID: D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/QuadraticMajorantEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quadratic logarithmic majorant bounds finite weighted sums through their first three moments. -/

import D5.S3.Analytic.Interpolation.EnvelopeKMonotone

open Set
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.Interpolation.QuadraticMajorantEnvelope

open TwoPointGridDominance EnvelopeKMonotone
open private logValue_hasDerivAt logValue_deriv_strictAnti radius_lt_mean from
  D5.S3.Analytic.Interpolation.EnvelopeKMonotone
open private hermite_majorant quadratic_derivatives from
  D5.S3.Analytic.Interpolation.HermiteUpperEnvelope

/-- The coefficient of the quadratic tangent at L and interpolating H. -/
def majorantCoeff (L H : ℝ) : ℝ :=
  (logValue H - logValue L - deriv logValue L * (H - L)) / (H - L) ^ 2

/-- The quadratic tangent at L and interpolating H. -/
def majorant (L H x : ℝ) : ℝ :=
  logValue L + deriv logValue L * (x - L) + majorantCoeff L H * (x - L) ^ 2

/-- The logarithmic secant lies strictly below the tangent at its positive left endpoint. -/
theorem logValue_sub_lt_tangent {L H : ℝ} (hL : 0 < L) (hLH : L < H) :
    logValue H - logValue L < deriv logValue L * (H - L) := by
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope logValue hLH
    (hlog.1.continuousOn.mono (fun t ht => hL.trans_le ht.1))
    (fun t ht => (logValue_hasDerivAt (hL.trans ht.1)).differentiableAt.differentiableWithinAt)
  have hlt := logValue_deriv_strictAnti hL (hL.trans hc.1) hc.1
  rw [hdc] at hlt
  exact (div_lt_iff₀ (sub_pos.mpr hLH)).mp hlt

/-- The interpolating quadratic has a strictly negative leading coefficient. -/
theorem majorant_coeff_neg {L H : ℝ} (hL : 0 < L) (hLH : L < H) :
    majorantCoeff L H < 0 :=
  div_neg_of_neg_of_pos (sub_neg.mpr (logValue_sub_lt_tangent hL hLH))
    (sq_pos_of_pos (sub_pos.mpr hLH))

/-- The majorant agrees with the logarithmic function at both interpolation nodes. -/
theorem majorant_at_nodes {L H : ℝ} (hLH : L < H) :
    majorant L H L = logValue L ∧ majorant L H H = logValue H := by
  constructor
  · simp [majorant]
  · dsimp [majorant, majorantCoeff]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr hLH.ne'))]
    ring

/-- The quadratic bounds the logarithmic function on the entire positive interval up to H. -/
theorem logValue_le_majorant {L H x : ℝ} (hL : 0 < L) (hLH : L < H)
    (hx : 0 < x) (hxH : x ≤ H) : logValue x ≤ majorant L H x := by
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  have hpd := quadratic_derivatives (logValue L) (deriv logValue L) (majorantCoeff L H) L
  have hnodes := majorant_at_nodes hLH
  exact hermite_majorant L H x logValue (majorant L H) hL hLH hx hxH hlog.1
    (by unfold majorant; fun_prop) hpd.2 hnodes.1 hpd.1 hnodes.2
    (fun t ht => (hlog.2 t ht).2.2.2)

#print axioms logValue_sub_lt_tangent
#print axioms majorant_coeff_neg
#print axioms majorant_at_nodes
#print axioms logValue_le_majorant

end D5.S3.Analytic.Interpolation.QuadraticMajorantEnvelope
