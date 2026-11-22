/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native A and B source germs and the phase on both D lips. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipMean

/-! The actual signed source branches in A and B and on both D lips. -/

set_option autoImplicit false

noncomputable section
open scoped Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSignedOverlap

-- The source branch comes from FourPoint/OriginalFourMSignedOverlap.lean
-- in the checked four-point-crossing-20261120 archive.
open OriginalGaussianExternalGenerators (sourceMode)
open OriginalGaussianExternalSignedCandidate (h)
open OriginalGaussianExternalAnalyticCandidate (b)
open FourPoint.OriginalFourMActualChart (Chart parameter periodRoot scaleRoot scale)

private def normalizedBranch (e : Bool) (u r : ℂ) : ℂ :=
  if e then h e u r / b u else h e u r / (b u * (1 - r))

/-- The source with the chart's chosen root of the period complement.
For D this root is the lower-lip choice for the radial parameter. -/
def chosenChartSource (c : Chart) (z : ℝ) (e : Bool) (u : ℂ) : ℂ :=
  (1 / (b u * (if e then 1 else periodRoot c z))) *
    normalizedBranch e u (parameter c z) ^ (-1 / 2 : ℂ)

open OriginalFourMSlitMean (slitMean slitMean_eq_sourceMode)
open OriginalFourMDLipMean (dLipMean)
open Complex (I)

private theorem invHalfPower_scale {a : ℝ} (ha : 0 < a) (x : ℂ) :
    ((a : ℂ) * x) ^ (-1 / 2 : ℂ) =
      (Real.sqrt a : ℂ)⁻¹ * x ^ (-1 / 2 : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Complex.zero_cpow (by norm_num : (-1 / 2 : ℂ) ≠ 0)]
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hroot : (a : ℂ) ^ (-1 / 2 : ℂ) = (Real.sqrt a : ℂ)⁻¹ := by
    rw [show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring, Complex.cpow_neg,
      Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    norm_num
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ha' hx), Complex.log_ofReal_mul ha hx,
    add_mul, Complex.exp_add, Complex.ofReal_log ha.le,
    ← Complex.cpow_def_of_ne_zero ha', ← Complex.cpow_def_of_ne_zero hx, hroot]

private theorem chosen_source_eq_slit_of_positive {c : Chart} {z a : ℝ} (ha : 0 < a)
    (hparam : 1 - parameter c (z : ℂ) = (a : ℂ))
    (hroot : periodRoot c z = (Real.sqrt a : ℂ)) (e : Bool) (u : ℂ) :
    chosenChartSource c z e u = slitMean e u (parameter c z) := by
  cases e
  · have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have harg : h false u (parameter c z) / b u =
        (a : ℂ) * normalizedBranch false u (parameter c z) := by
      simp only [normalizedBranch, Bool.false_eq_true, ite_false, hparam, div_eq_mul_inv,
        mul_inv_rev]
      calc
        _ = (h false u (parameter c z) * (b u)⁻¹) * ((a : ℂ) * (a : ℂ)⁻¹) := by
          rw [mul_inv_cancel₀ ha', mul_one]
        _ = _ := by ring
    rw [slitMean, harg, invHalfPower_scale ha, chosenChartSource]
    simp only [Bool.false_eq_true, ite_false, hroot, one_div, mul_inv_rev]
    ring
  · simp [chosenChartSource, normalizedBranch, slitMean, one_div]

/-- Where A or B is in the original radial disk, the chosen branch agrees
with the native source on a neighborhood of the spatial origin. -/
theorem chosen_chart_source_eq_native {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (c : Chart) (hc : c = .A ∨ c = .B) (e : Bool)
    (hr : ‖parameter c (z : ℂ)‖ < 1) :
    chosenChartSource c z e =ᶠ[𝓝 0] (fun u => sourceMode e u (parameter c z)) := by
  have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ + ‖parameter c (z : ℂ)‖ < 1 :=
    (isOpen_lt (continuous_norm.add continuous_const) continuous_const).mem_nhds
      (by simpa using hr)
  filter_upwards [hsmall] with u hu
  rw [← slitMean_eq_sourceMode e hu]
  rcases hc with rfl | rfl
  · apply chosen_source_eq_slit_of_positive (inv_pos.mpr hz)
    · simp [parameter, Complex.ofReal_inv]
    · change (Real.sqrt z : ℂ)⁻¹ = (Real.sqrt z⁻¹ : ℂ)
      rw [Real.sqrt_inv, Complex.ofReal_inv]
  · apply chosen_source_eq_slit_of_positive (sub_pos.mpr hz1)
    · simp [parameter]
    · rfl

/-- The chosen D source agrees with the lower D lip. The other lip
reverses the inward source and preserves the outgoing source. -/
theorem dLipMean_eq_chosen_chart_source {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (upperA e : Bool) (u : ℂ) :
    dLipMean upperA e u (parameter .D (z : ℂ)) =
      (if upperA || e then 1 else -1) * chosenChartSource .D z e u := by
  cases e
  · let a := z⁻¹ - 1
    have ha : 0 < a := sub_pos.mpr ((one_lt_inv₀ hz).2 hz1)
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hparam : 1 - parameter .D (z : ℂ) = -(a : ℂ) := by
      simp [a, parameter, sub_eq_add_neg]
    have hroot : periodRoot .D z = I * (Real.sqrt a : ℂ) := by
      have he : a = (1 - z) / z := by
        dsimp [a]
        field_simp [hz.ne']
      change I * (Real.sqrt (1 - z) : ℂ) / (Real.sqrt z : ℂ) = _
      rw [he, Real.sqrt_div (sub_nonneg.mpr hz1.le), Complex.ofReal_div, mul_div_assoc]
    have harg : -(h false u (parameter .D (z : ℂ)) / b u) =
        (a : ℂ) * normalizedBranch false u (parameter .D (z : ℂ)) := by
      simp only [normalizedBranch, Bool.false_eq_true, ite_false, hparam, div_eq_mul_inv,
        mul_neg, inv_neg, mul_inv_rev]
      calc
        _ = -((h false u (parameter .D (z : ℂ)) * (b u)⁻¹) * ((a : ℂ) * (a : ℂ)⁻¹)) := by
          rw [mul_inv_cancel₀ ha', mul_one]
        _ = _ := by ring
    calc
      dLipMean upperA false u (parameter .D (z : ℂ)) =
          (b u)⁻¹ * ((if upperA then -I else I) *
            (-(h false u (parameter .D (z : ℂ)) / b u)) ^ (-1 / 2 : ℂ)) := rfl
      _ = _ := by
        rw [harg, invHalfPower_scale ha]
        cases upperA <;>
          simp [chosenChartSource, hroot, Complex.inv_I, one_div, mul_inv_rev] <;> ring
  · change slitMean true u (parameter .D (z : ℂ)) = _
    simp [chosenChartSource, slitMean, normalizedBranch, one_div]

/-- The complementary argument is nonzero on each physical overlap chart. -/
theorem chart_parameter_ne_one {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (c : Chart) :
    1 - parameter c (z : ℂ) ≠ 0 := by
  have h0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h1 : (z : ℂ) ≠ 1 := by exact_mod_cast hz1.ne
  cases c
  · simpa [parameter] using inv_ne_zero h0
  · exact sub_ne_zero.mpr h1.symm
  · exact sub_ne_zero.mpr (fun h => h1 (inv_eq_one.mp h.symm))

/-- The chosen source is analytic with its period-root normalization at the puncture. -/
theorem chosen_chart_source_at_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (c : Chart) (e : Bool) :
    AnalyticAt ℂ (chosenChartSource c z e) 0 ∧
      chosenChartSource c z e 0 = (if e then 1 else periodRoot c z)⁻¹ := by
  have hd := chart_parameter_ne_one hz hz1 c
  have hroots : scaleRoot c z .P ^ 2 = scale c z .P ∧
      periodRoot c z ^ 2 = 1 - parameter c z :=
    FourPoint.OriginalFourMActualChart.chosen_roots hz hz1 c .P
  have hroot : periodRoot c z ≠ 0 := by
    intro h0
    exact hd (by simpa [h0] using hroots.2.symm)
  have hn₀ : normalizedBranch e 0 (parameter c z) = 1 := by
    cases e <;> simp [normalizedBranch, h, b, hd]
  have hn : AnalyticAt ℂ (fun u => normalizedBranch e u (parameter c z)) 0 := by
    cases e
    · exact (analyticAt_const.sub analyticAt_id).div
        ((analyticAt_const.sub analyticAt_id).mul analyticAt_const) (by simpa [b] using hd)
    · exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
        (analyticAt_const.sub analyticAt_id) (by simp [b])
  have hb : AnalyticAt ℂ (fun u => b u * (if e then 1 else periodRoot c z)) 0 :=
    (analyticAt_const.sub analyticAt_id).mul analyticAt_const
  have hb₀ : b 0 * (if e then 1 else periodRoot c z) ≠ 0 := by
    cases e <;> simp [b, hroot]
  refine ⟨(analyticAt_const.div hb hb₀).mul
    (hn.cpow analyticAt_const (by rw [hn₀]; exact Complex.one_mem_slitPlane)), ?_⟩
  simp [chosenChartSource, hn₀, b]

/-- Away from zeros of the two native factors, squaring removes the chosen phase. -/
theorem chosen_chart_source_square {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (c : Chart) (e : Bool) {u : ℂ} (hb : b u ≠ 0) (hh : h e u (parameter c z) ≠ 0) :
    chosenChartSource c z e u ^ 2 = 1 / (b u * h e u (parameter c z)) := by
  have hd := chart_parameter_ne_one hz hz1 c
  have hroots : scaleRoot c z .P ^ 2 = scale c z .P ∧
      periodRoot c z ^ 2 = 1 - parameter c z :=
    FourPoint.OriginalFourMActualChart.chosen_roots hz hz1 c .P
  have hroot := hroots.2
  have hpow (v : ℂ) : (v ^ (-1 / 2 : ℂ)) ^ 2 = 1 / v := by
    rw [← Complex.cpow_mul_nat]
    norm_num [Complex.cpow_neg_one]
  unfold chosenChartSource
  rw [mul_pow, div_pow, hpow, mul_pow]
  cases e <;> simp only [normalizedBranch, Bool.false_eq_true, ite_false, ite_true,
    hroot, one_pow, mul_one, one_div_div] <;> field_simp [hb, hh, hd]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSignedOverlap
