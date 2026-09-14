/- GID: D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/QuadraticMajorantEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quadratic logarithmic majorant bounds finite weighted sums by three moments. -/

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

/-- A finite weighted quadratic sum is determined by mass, mean, and centered second moment. -/
theorem weighted_quadratic_sum {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (K μ r A B C V W : ℝ)
    (hmass : ∑ i, w i = K) (hmean : ∑ i, w i * x i = K * μ)
    (hvar : ∑ i, w i * (x i - μ) ^ 2 = W) (hV : V = K * (K - 1) * r ^ 2) :
    let p := fun t => A + B * (t - (μ - r)) + C * (t - (μ - r)) ^ 2
    ∑ i, w i * p (x i) =
      p (μ + (K - 1) * r) + (K - 1) * p (μ - r) + C * (W - V) := by
  have hcenter : ∑ i, w i * (x i - μ) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, hmean]
    ring
  have hfirst : ∑ i, w i * (x i - (μ - r)) = K * r := by
    simp_rw [show ∀ i, w i * (x i - (μ - r)) =
      w i * (x i - μ) + w i * r from fun i => by ring]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcenter, hmass, zero_add]
  have hsecond : ∑ i, w i * (x i - (μ - r)) ^ 2 = W + K * r ^ 2 := by
    simp_rw [show ∀ i, w i * (x i - (μ - r)) ^ 2 =
      w i * (x i - μ) ^ 2 + 2 * r * (w i * (x i - μ)) + w i * r ^ 2
      from fun i => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hcenter, hvar, hmass]
    ring
  dsimp only
  calc
    _ = K * A + B * (K * r) + C * (W + K * r ^ 2) := by
      simp_rw [show ∀ i, w i * (A + B * (x i - (μ - r)) + C * (x i - (μ - r)) ^ 2) =
        w i * A + B * (w i * (x i - (μ - r))) + C * (w i * (x i - (μ - r)) ^ 2)
        from fun i => by ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, ← Finset.mul_sum, hmass, hfirst, hsecond]
    _ = _ := by rw [hV]; ring

private theorem reference_nodes_domain {k : ℕ} (hk : 2 ≤ k) {μ V : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hupper : V < (k : ℝ) * ((k : ℝ) - 1) * μ ^ 2) :
    let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
    0 < μ - r ∧ μ - r < μ + ((k : ℝ) - 1) * r ∧
      V = (k : ℝ) * ((k : ℝ) - 1) * r ^ 2 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := mul_pos hkpos (by linarith)
  have hr := Real.sqrt_pos.mpr (div_pos hV hden)
  refine ⟨sub_pos.mpr (radius_lt_mean hk hμ hupper), ?_, ?_⟩
  · nlinarith [mul_pos hkpos hr]
  · rw [Real.sq_sqrt (div_nonneg hV.le hden.le)]
    exact (mul_div_cancel₀ V hden.ne').symm

/-- The weighted majorant sum equals the reference envelope plus the variance correction. -/
theorem weighted_majorant_sum {ι : Type*} [Fintype ι] {k : ℕ} (hk : 2 ≤ k)
    (w x : ι → ℝ) {μ V V_M : ℝ} (hμ : 0 < μ) (hV : 0 < V)
    (hupper : V < (k : ℝ) * ((k : ℝ) - 1) * μ ^ 2)
    (hmass : ∑ i, w i = (k : ℝ)) (hmean : ∑ i, w i * x i = (k : ℝ) * μ)
    (hvar : ∑ i, w i * (x i - μ) ^ 2 = V_M) :
    let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
    let L := μ - r
    let H := μ + ((k : ℝ) - 1) * r
    ∑ i, w i * majorant L H (x i) = psiK k μ V + majorantCoeff L H * (V_M - V) := by
  dsimp only
  let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
  let L := μ - r
  let H := μ + ((k : ℝ) - 1) * r
  have hd := reference_nodes_domain hk hμ hV hupper
  have hnodes := majorant_at_nodes hd.2.1
  have hsum := weighted_quadratic_sum w x (k : ℝ) μ r (logValue L) (deriv logValue L)
    (majorantCoeff L H) V V_M hmass hmean hvar hd.2.2
  change ∑ i, w i * majorant L H (x i) =
    majorant L H H + ((k : ℝ) - 1) * majorant L H L +
      majorantCoeff L H * (V_M - V) at hsum
  rw [hnodes.1, hnodes.2] at hsum
  exact hsum

/-- Nonnegative weights on positive support up to H obey the reference moment bound. -/
theorem weighted_majorant_bound {ι : Type*} [Fintype ι] {k : ℕ} (hk : 2 ≤ k)
    (w x : ι → ℝ) {μ V V_M : ℝ} (hμ : 0 < μ) (hV : 0 < V)
    (hupper : V < (k : ℝ) * ((k : ℝ) - 1) * μ ^ 2)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 < x i)
    (hxH : ∀ i, x i ≤ μ + ((k : ℝ) - 1) * Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1))))
    (hmass : ∑ i, w i = (k : ℝ)) (hmean : ∑ i, w i * x i = (k : ℝ) * μ)
    (hvar : ∑ i, w i * (x i - μ) ^ 2 = V_M) :
    let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
    let L := μ - r
    let H := μ + ((k : ℝ) - 1) * r
    ∑ i, w i * logValue (x i) ≤ psiK k μ V + majorantCoeff L H * (V_M - V) := by
  dsimp only
  rw [← weighted_majorant_sum hk w x hμ hV hupper hmass hmean hvar]
  have hd := reference_nodes_domain hk hμ hV hupper
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
    (logValue_le_majorant hd.1 hd.2.1 (hx i) (hxH i)) (hw i))

/-- A weighted variance at least the reference variance removes the nonpositive correction. -/
theorem weighted_le_psiK_of_variance_ge {ι : Type*} [Fintype ι] {k : ℕ} (hk : 2 ≤ k)
    (w x : ι → ℝ) {μ V V_M : ℝ} (hμ : 0 < μ) (hV : 0 < V)
    (hupper : V < (k : ℝ) * ((k : ℝ) - 1) * μ ^ 2)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 < x i)
    (hxH : ∀ i, x i ≤ μ + ((k : ℝ) - 1) * Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1))))
    (hmass : ∑ i, w i = (k : ℝ)) (hmean : ∑ i, w i * x i = (k : ℝ) * μ)
    (hvar : ∑ i, w i * (x i - μ) ^ 2 = V_M) (hfloor : V ≤ V_M) :
    ∑ i, w i * logValue (x i) ≤ psiK k μ V := by
  have hd := reference_nodes_domain hk hμ hV hupper
  have hc := majorant_coeff_neg hd.1 hd.2.1
  have hbound := weighted_majorant_bound hk w x hμ hV hupper hw hx hxH hmass hmean hvar
  exact hbound.trans (add_le_of_nonpos_right
    (mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.mpr hfloor)))

#print axioms weighted_quadratic_sum
#print axioms weighted_majorant_sum
#print axioms weighted_majorant_bound
#print axioms weighted_le_psiK_of_variance_ge
#print axioms logValue_sub_lt_tangent
#print axioms majorant_coeff_neg
#print axioms majorant_at_nodes
#print axioms logValue_le_majorant

end D5.S3.Analytic.Interpolation.QuadraticMajorantEnvelope
