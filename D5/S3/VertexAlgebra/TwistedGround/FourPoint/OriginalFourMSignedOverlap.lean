/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native A and B source germs and the phase on both D lips. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipMean
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedCovariance
import D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial

/-! The actual signed source branches in A and B and on both D lips. -/

set_option autoImplicit false

noncomputable section
open scoped Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSignedOverlap

-- The source branch comes from FourPoint/OriginalFourMSignedOverlap.lean
-- in the checked four-point-crossing-20261120 archive.
open OriginalGaussianExternalGenerators (sourceMode)
open OriginalGaussianExternalSignedCandidate (G h cauchy rho E K N rationalT)
open OriginalGaussianExternalAnalyticCandidate (b)
open OriginalGaussianExternalCandidateCore (rightChart leftChart)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)
open FourPoint.OriginalFourMActualChart
  (Chart parameter pullB pullD spatialKernel periodRoot scaleRoot scale)
open OriginalFourMPeriodSource (chartCorrection dPeriod)

/-- The geometric spatial kernel with the chart period correction. -/
def covOnChart (upperA : Bool) (c : Chart) (z x X : ℂ) : ℂ :=
  spatialKernel (1 - parameter c z) x X - chartCorrection upperA c z

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

open private legMap legMap_chart spatial_legMap legMap_sub_one legMap_involution
  from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedCovariance

private theorem chart_parameter_ne_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (c : Chart) :
    parameter c (z : ℂ) ≠ 0 := by
  have h0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h1 : (z : ℂ) ≠ 1 := by exact_mod_cast hz1.ne
  cases c
  · exact sub_ne_zero.mpr (fun h => h1 (inv_eq_one.mp h.symm))
  · exact h0
  · exact inv_ne_zero h0

/-- The chosen source multiplied by its local branch factor. -/
def chartW (c : Chart) (z : ℝ) (e : Bool) (u : ℂ) : ℂ :=
  h e u (parameter c z) * chosenChartSource c z e u

private theorem chartW_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (c : Chart) (e : Bool) :
    chartW c z e 0 = if e then 1 else periodRoot c z := by
  have hd := chart_parameter_ne_one hz hz1 c
  have hroots : scaleRoot c z .S ^ 2 = scale c z .S ∧
      periodRoot c z ^ 2 = 1 - parameter c z :=
    FourPoint.OriginalFourMActualChart.chosen_roots hz hz1 c .S
  have hs := hroots.2
  have h0 : periodRoot c z ≠ 0 := by
    intro he
    exact hd (by simpa [he] using hs.symm)
  unfold chartW
  rw [(chosen_chart_source_at_zero hz hz1 c e).2]
  cases e
  · simp only [h, Bool.false_eq_true, ite_false, sub_zero]
    rw [← hs, pow_two,
      mul_assoc, mul_inv_cancel₀ h0, mul_one]
  · simp [h]

/-- The weighted source is analytic at the native puncture. -/
theorem chartW_analytic {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (c : Chart) (e : Bool) :
    AnalyticAt ℂ (chartW c z e) 0 := by
  have hh : AnalyticAt ℂ (fun u => h e u (parameter c z)) 0 := by
    cases e
    · exact analyticAt_const.sub analyticAt_id
    · exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  exact hh.mul ((chosen_chart_source_at_zero hz hz1 c e).1)

/-- The sum of the two weighted sources is nonzero at the common native origin. -/
theorem chartW_sum_ne_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (c : Chart) (e f : Bool) : chartW c z e 0 + chartW c z f 0 ≠ 0 := by
  have hroots : scaleRoot c z .S ^ 2 = scale c z .S ∧
      periodRoot c z ^ 2 = 1 - parameter c z :=
    FourPoint.OriginalFourMActualChart.chosen_roots hz hz1 c .S
  have hs := hroots.2
  have hd := chart_parameter_ne_one hz hz1 c
  have hr := chart_parameter_ne_zero hz hz1 c
  have h0 : periodRoot c z ≠ 0 := fun he => hd (by simpa [he] using hs.symm)
  have h1 : periodRoot c z + 1 ≠ 0 := by
    intro he
    have he' : periodRoot c z = -1 := eq_neg_of_add_eq_zero_left he
    rw [he', neg_sq, one_pow] at hs
    exact hr (by linear_combination hs)
  rw [chartW_zero hz hz1 c e, chartW_zero hz hz1 c f]
  have h1' : 1 + periodRoot c z ≠ 0 := by rwa [add_comm]
  cases e <;> cases f <;> simp [h1, h1', h0, ← two_mul]

/-- The concrete continued J-plus-free and minus-T generators. Equal
orientations use the regular J formula directly at the diagonal. -/
def chartCovariance (upperA : Bool) (c : Chart) (z : ℝ) (l k e f : Bool)
    (u v : ℂ) : ℂ :=
  let r := parameter c z
  let C := chartCorrection upperA c z
  let m := chosenChartSource c z e u * chosenChartSource c z f v
  if l = k then
    m * (r / 4 - C + r ^ 2 * rho e f u v /
      (4 * b u * b v * (chartW c z e u + chartW c z f v) ^ 2)) +
      (if e = f then 0 else cauchy e f u v)
  else - (m * (rationalT e f u v r - C))

/-- At each actual A, B and D parameter, every signed generator is
jointly analytic at the two external punctures, including the coincident
same-orientation puncture. -/
theorem chart_covariance_analytic {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (upperA : Bool) (c : Chart) (l k e f : Bool) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => chartCovariance upperA c z l k e f p.1 p.2) (0, 0) := by
  let r := parameter c (z : ℂ)
  let x : ℂ × ℂ := (0, 0)
  have hu : AnalyticAt ℂ Prod.fst x := analyticAt_fst
  have hv : AnalyticAt ℂ Prod.snd x := analyticAt_snd
  have hMe : AnalyticAt ℂ (fun p : ℂ × ℂ => chosenChartSource c z e p.1) x :=
    AnalyticAt.comp (f := Prod.fst) (x := x) ((chosen_chart_source_at_zero hz hz1 c e).1) hu
  have hMf : AnalyticAt ℂ (fun p : ℂ × ℂ => chosenChartSource c z f p.2) x :=
    AnalyticAt.comp (f := Prod.snd) (x := x) ((chosen_chart_source_at_zero hz hz1 c f).1) hv
  have hWe : AnalyticAt ℂ (fun p : ℂ × ℂ => chartW c z e p.1) x :=
    AnalyticAt.comp (f := Prod.fst) (x := x) (chartW_analytic hz hz1 c e) hu
  have hWf : AnalyticAt ℂ (fun p : ℂ × ℂ => chartW c z f p.2) x :=
    AnalyticAt.comp (f := Prod.snd) (x := x) (chartW_analytic hz hz1 c f) hv
  have hm := hMe.mul hMf
  have hW := hWe.add hWf
  have hb₁ : AnalyticAt ℂ (fun p : ℂ × ℂ => b p.1) x := analyticAt_const.sub hu
  have hb₂ : AnalyticAt ℂ (fun p : ℂ × ℂ => b p.2) x := analyticAt_const.sub hv
  have hrho : AnalyticAt ℂ (fun p : ℂ × ℂ => rho e f p.1 p.2) x := by
    by_cases hef : e = f
    · simp only [rho, hef, ite_true]
      exact hu.add hv
    · simp only [rho, hef, ite_false]
      exact (analyticAt_const.add (hu.mul hv)).neg
  have he : AnalyticAt ℂ (fun p : ℂ × ℂ => E e f p.1 p.2 r) x := by
    have hk : AnalyticAt ℂ (fun p : ℂ × ℂ => K e f p.1 p.2) x := by
      cases e <;> cases f <;> simp only [K, Bool.false_eq_true, ite_false, ite_true]
      · exact analyticAt_const
      · exact hv.neg
      · exact hu.neg
      · exact hu.mul hv
    exact (hb₁.mul hb₂).sub (analyticAt_const.mul hk)
  have he0 : E e f 0 0 r ≠ 0 := by
    have hd := chart_parameter_ne_one hz hz1 c
    cases e <;> cases f <;> simp [E, b, K, r, hd]
  by_cases hl : l = k
  · have hden : AnalyticAt ℂ (fun p : ℂ × ℂ => 4 * b p.1 * b p.2 *
        (chartW c z e p.1 + chartW c z f p.2) ^ 2) x :=
        ((analyticAt_const.mul hb₁).mul hb₂).mul (hW.pow 2)
    have hden0 : 4 * b (0 : ℂ) * b (0 : ℂ) *
        (chartW c z e 0 + chartW c z f 0) ^ 2 ≠ 0 := by
      simpa [b] using chartW_sum_ne_zero hz hz1 c e f
    have hj : AnalyticAt ℂ (fun p : ℂ × ℂ =>
        chosenChartSource c z e p.1 * chosenChartSource c z f p.2 *
          (r / 4 - chartCorrection upperA c z + r ^ 2 * rho e f p.1 p.2 /
            (4 * b p.1 * b p.2 * (chartW c z e p.1 + chartW c z f p.2) ^ 2))) x :=
      hm.mul (analyticAt_const.add ((analyticAt_const.mul hrho).div hden hden0))
    by_cases hef : e = f
    · simpa [chartCovariance, hl, hef, r] using hj
    · have hc : AnalyticAt ℂ (fun p : ℂ × ℂ => cauchy e f p.1 p.2) x := by
        unfold cauchy
        apply hrho.div
        · simp only [G, hef, ite_false]
          exact analyticAt_const.mul ((analyticAt_const.sub (hu.mul hv)).pow 2)
        · simp [x, G, hef]
      simp only [chartCovariance, hl, hef, ite_true, ite_false]
      exact hj.add hc
  · have hn : AnalyticAt ℂ (fun p : ℂ × ℂ => N e f p.1 p.2 r) x := by
      cases e <;> cases f <;> simp only [N, Bool.false_eq_true, ite_false, ite_true]
      · exact analyticAt_const.add (hu.mul hv)
      · exact (hu.add (analyticAt_const.mul hv)).neg
      · exact ((analyticAt_const.mul hu).add hv).neg
      · exact analyticAt_const.add ((analyticAt_const.mul hu).mul hv)
    have hrT : AnalyticAt ℂ (fun p : ℂ × ℂ => rationalT e f p.1 p.2 r) x := by
      exact ((analyticAt_const.mul hn).div (analyticAt_const.mul he)
        (mul_ne_zero (by norm_num) he0)).add
          (((analyticAt_const.mul hu).mul hv).div (he.pow 2) (pow_ne_zero 2 he0))
    simp only [chartCovariance, hl, ite_false]
    exact (hm.mul (hrT.sub analyticAt_const)).neg

private theorem chart_source_normalization {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (c : Chart) (e : Bool) {u : ℂ} (hb : b u ≠ 0) (hh : h e u (parameter c z) ≠ 0) :
    chartW c z e u ^ 2 * b u = h e u (parameter c z) ∧
    chosenChartSource c z e u * b u * chartW c z e u = 1 ∧ chartW c z e u ≠ 0 := by
  have hs : chosenChartSource c z e u ^ 2 = 1 / (b u * h e u (parameter c z)) :=
    chosen_chart_source_square hz hz1 c e hb hh
  have hW : chartW c z e u ^ 2 * b u = h e u (parameter c z) := by
    unfold chartW
    rw [mul_pow, hs]
    field_simp [hb, hh]
  refine ⟨hW, ?_, ?_⟩
  · calc
      _ = chosenChartSource c z e u ^ 2 * (b u * h e u (parameter c z)) := by unfold chartW; ring
      _ = 1 := by rw [hs]; exact one_div_mul_cancel (mul_ne_zero hb hh)
  · intro he
    rw [he, zero_pow (by decide : 2 ≠ 0), zero_mul] at hW
    exact hh hW.symm

private theorem chart_spatial_overlap {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (upperA : Bool) (c : Chart) (e f : Bool) {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hbu : b u ≠ 0) (hbv : b v ≠ 0)
    (hhu : h e u (parameter c z) ≠ 0) (hhv : h f v (parameter c z) ≠ 0)
    (hW : chartW c z e u + chartW c z f v ≠ 0)
    (hG : G e f u v ≠ 0) :
    let r := parameter c z
    let C := chartCorrection upperA c z
    let m := chosenChartSource c z e u * chosenChartSource c z f v
    ∀ l, chartCovariance upperA c z l l e f u v =
        m * (spatialKernel (1 - r) (rightChart e u) (rightChart f v) - C) -
        (if e = f then cauchy e f u v else 0) := by
  dsimp only
  obtain ⟨hU, hmu, hU0⟩ := chart_source_normalization hz hz1 c e hbu hhu
  obtain ⟨hV, hmv, hV0⟩ := chart_source_normalization hz hz1 c f hbv hhv
  have hJ := OriginalGaussianExternalSignedCandidate.regularJ_chart_algebra
    e f hbu hbv hW hG hU0 hV0 hU hV hmu hmv
  rw [ratJ_spatial e f hu hv hG] at hJ
  intro l
  rw [chartCovariance, ite_eq_left rfl]
  by_cases hef : e = f
  · simp only [hef, ite_true, add_zero]
    rw [hef] at hJ
    linear_combination -hJ
  · simp only [hef, ite_false, sub_zero]
    linear_combination -hJ

/-- Restoring the same-slot Cauchy term gives the geometric covariance with
both signed sources at the actual native elliptic coordinates. -/
theorem signed_spatial (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (l k e f : Bool) {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hbu : b u ≠ 0) (hbv : b v ≠ 0)
    (hhu : h e u (parameter c x) ≠ 0) (hhv : h f v (parameter c x) ≠ 0)
    (hW : chartW c x e u + chartW c x f v ≠ 0) (hE : E e f u v (parameter c x) ≠ 0)
    (hG : l = k → G e f u v ≠ 0)
    (hsep : (if l then leftChart e (parameter c x) u else rightChart e u) -
      (if k then leftChart f (parameter c x) v else rightChart f v) ≠ 0) :
    let r := parameter c (x : ℂ)
    let X := if l then leftChart e r u else rightChart e u
    let Y := if k then leftChart f r v else rightChart f v
    chartCovariance upperA c x l k e f u v + (if l = k ∧ e = f then cauchy e f u v else 0) =
      (legSign l * chosenChartSource c x e u) * (legSign k * chosenChartSource c x f v) *
        covOnChart upperA c x X Y := by
  dsimp only
  let r := parameter c (x : ℂ)
  have hright (e : Bool) {v : ℂ} (hv : v ≠ 0) (hbv : b v ≠ 0) :
      rightChart e v - 1 ≠ 0 := by
    cases e
    · exact fun he => hbv (by simpa [rightChart, b] using congrArg Neg.neg he)
    · simp only [rightChart, ite_true, one_div]
      intro he
      exact hbv (by simp [b, inv_eq_one.mp (sub_eq_zero.mp he)])
  have hX := hright e hu hbu
  have hY := hright f hv hbv
  have hleg (e : Bool) {u : ℂ} (hu : u ≠ 0) (hbu : b u ≠ 0) :
      legMap r (rightChart e u) = leftChart e r u :=
    legMap_chart e hu (fun he => hbu (by simp [b, he]))
  have hr : r ≠ 0 := chart_parameter_ne_zero hx hx1 c
  by_cases hl : l = k
  · subst k
    have hJ := chart_spatial_overlap hx hx1 upperA c e f
      hu hv hbu hbv hhu hhv hW (hG rfl) l
    cases l
    · simpa [covOnChart, legSign, sub_add_cancel] using congrArg
        (fun a => a + (if e = f then cauchy e f u v else 0)) hJ
    · have hSep : leftChart e r u - leftChart f r v ≠ 0 := by simpa using hsep
      have hrr : rightChart e u - rightChart f v ≠ 0 := by
        intro he
        apply hSep
        apply sub_eq_zero.mpr
        rw [← hleg e hu hbu, ← hleg f hv hbv]
        exact congrArg (legMap r) (sub_eq_zero.mp he)
      simp only [ite_true]
      rw [show leftChart e r u = legMap r (rightChart e u) from (hleg e hu hbu).symm,
          show leftChart f r v = legMap r (rightChart f v) from (hleg f hv hbv).symm,
          covOnChart, spatial_legMap hr hX hY hrr]
      simpa [legSign, sub_add_cancel] using congrArg
        (fun a => a + (if e = f then cauchy e f u v else 0)) hJ
  · have hT := ratT_spatial e f hu hbv hE
    rw [chartCovariance, ite_eq_right hl, hT, ite_eq_right (fun he => hl he.1)]
    cases l <;> cases k
    · exact (hl rfl).elim
    · simp only [covOnChart, Bool.false_eq_true, ite_false, ite_true, legSign, one_mul,
        add_zero, mul_neg, neg_mul]
    · have hSep : leftChart e r u - rightChart f v ≠ 0 := by simpa using hsep
      have hcross : rightChart e u - leftChart f r v ≠ 0 := by
        intro he
        apply hSep
        rw [← hleg e hu hbu, sub_eq_zero.mpr (by
          rw [sub_eq_zero.mp he, ← hleg f hv hbv, legMap_involution hr hY])]
      have hg := spatial_legMap hr hX
        (by rw [← hleg f hv hbv, legMap_sub_one hY]; exact div_ne_zero hr hY) hcross
      rw [hleg e hu hbu, ← hleg f hv hbv, legMap_involution hr hY] at hg
      simp only [covOnChart, legSign, Bool.false_eq_true, ite_true, ite_false, one_mul,
        neg_mul, add_zero]
      rw [hg, hleg f hv hbv]
    · exact (hl rfl).elim


end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSignedOverlap
