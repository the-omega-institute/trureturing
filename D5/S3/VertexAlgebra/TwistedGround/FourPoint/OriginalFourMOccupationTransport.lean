/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical inverse-coordinate transport of the original signed Gaussian. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy

/-! Inverse half-coordinate transport for the signed four-point Gaussian. -/

set_option autoImplicit false

noncomputable section
open Complex Filter
open scoped Topology BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMOccupationTransport

open OriginalFourMActualChart
  (Chart Puncture parameter scale scaleRoot loweringParameter periodRoot halfDifferentialAt
    relativeB relativeD)
open OriginalFourMSignedOverlap (legSign chartCovariance)
open OriginalGaussianExternalAnalyticCandidate (b)
open OriginalGaussianExternalSignedCandidate (h cauchy)
open private chartPuncture chosenChartSource analyticAt_local_cpow normalizedSource_square
  chart_parameter_ne_one chart_parameter_ne_zero from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open private rawLocal halfJacobian freeCorrection chartScale bLift from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private scale_ne leftP leftQ rightS rightSign outgoing from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

/-- The native leg and orientation of a fixed physical puncture. -/
def flags : Chart → Puncture → Bool × Bool
  | _, .S => (true, true)
  | .A, .P | .B, .Q | .D, .P => (false, false)
  | .A, .Q | .B, .R | .D, .R => (false, true)
  | .A, .R | .B, .P | .D, .Q => (true, false)

private theorem chartPuncture_flags (c : Chart) (i : Puncture) :
    chartPuncture c (flags c i).1 (flags c i).2 = i := by
  cases c <;> cases i <;> rfl

/-- The normalized local root in the inverse lowering coordinate. -/
def inverseRoot (c : Chart) (x : ℝ) (i : Puncture) (u : ℂ) : ℂ :=
  (1 - loweringParameter c i * rawLocal c x i u) ^ (1 / 2 : ℂ)

private theorem inverseRoot_sq (c : Chart) (x : ℝ) (i : Puncture) (u : ℂ) :
    inverseRoot c x i u ^ 2 = 1 - loweringParameter c i * rawLocal c x i u := by
  unfold inverseRoot
  rw [← Complex.cpow_mul_nat]
  norm_num

private theorem rawLocal_analytic {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) : AnalyticAt ℂ (rawLocal c x i) 0 :=
  analyticAt_id.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    (by simpa using scale_ne hx hx1 c i)

private theorem inverseRoot_zero (c : Chart) (x : ℝ) (i : Puncture) :
    inverseRoot c x i 0 = 1 := by simp [inverseRoot, rawLocal]

private theorem inverseRoot_analytic {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) : AnalyticAt ℂ (inverseRoot c x i) 0 :=
  analyticAt_local_cpow
    (analyticAt_const.sub (analyticAt_const.mul (rawLocal_analytic hx hx1 c i)))
    (by simp [rawLocal])

private theorem root_ne {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) : scaleRoot c x i ≠ 0 := by
  intro hr
  exact scale_ne hx hx1 c i (by simpa [hr] using
    (OriginalFourMActualChart.chosen_roots hx hx1 c i).1.symm)

/-- The signed native source in the common physical coordinate at one puncture. -/
def physicalSource (c : Chart) (x : ℝ) (i : Puncture) (u : ℂ) : ℂ :=
  legSign (flags c i).1 * chosenChartSource c x (flags c i).2 (rawLocal c x i u) /
    halfJacobian c x i (inverseRoot c x i u)

private theorem physicalSource_analytic {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) : AnalyticAt ℂ (physicalSource c x i) 0 := by
  have hsource₀ : AnalyticAt ℂ (chosenChartSource c x (flags c i).2) (rawLocal c x i 0) := by
    simpa only [rawLocal, zero_div] using
      OriginalFourMSignedOverlap.chosen_chart_source_analytic hx hx1 c (flags c i).2
  have hsource := hsource₀.comp (rawLocal_analytic hx hx1 c i)
  have hJ : AnalyticAt ℂ (fun u => halfJacobian c x i (inverseRoot c x i u)) 0 :=
    analyticAt_const.div ((inverseRoot_analytic hx hx1 c i).pow 3)
      (by simp [inverseRoot_zero])
  exact (analyticAt_const.mul hsource).div hJ
    (by simp [halfJacobian, inverseRoot_zero, root_ne hx hx1])

private theorem physicalSource_zero {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) : physicalSource c x i 0 = halfDifferentialAt c x i := by
  simpa [physicalSource, rawLocal, halfJacobian, inverseRoot_zero, chartPuncture_flags] using
    OriginalFourMSignedOverlap.chart_source_at_puncture hx hx1 c (flags c i).1 (flags c i).2

private theorem physicalSource_sq {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) :
    (fun u => physicalSource c x i u ^ 2) =ᶠ[𝓝 (0 : ℂ)]
      (fun u => let v := rawLocal c x i u
                (1 - loweringParameter c i * v) ^ 3 /
                  (scale c x i * (b v * h (flags c i).2 v (parameter c x)))) := by
  let v := rawLocal c x i
  let e := (flags c i).2
  have hv := rawLocal_analytic hx hx1 c i
  have hb : ContinuousAt (fun u => b (v u)) 0 := continuousAt_const.sub hv.continuousAt
  have hh : ContinuousAt (fun u => h e (v u) (parameter c x)) 0 := by
    cases e <;> simp only [h, Bool.false_eq_true, ite_false, ite_true]
    · exact continuousAt_const.sub hv.continuousAt
    · exact continuousAt_const.sub (continuousAt_const.mul hv.continuousAt)
  have hh₀ : h e (v 0) (parameter c x) ≠ 0 := by
    cases e <;> simp [v, rawLocal, h, chart_parameter_ne_one hx hx1 c]
  filter_upwards [hb.eventually_ne (y := (0 : ℂ)) (by simp [b, v, rawLocal]),
    hh.eventually_ne hh₀] with u hbu hhu
  have hs := normalizedSource_square (r := parameter c x) (u := v u) e
    (OriginalFourMActualChart.chosen_roots hx hx1 c i).2
    (chart_parameter_ne_one hx hx1 c) hbu hhu
  have hl : legSign (flags c i).1 ^ 2 = 1 := by cases (flags c i).1 <;> norm_num [legSign]
  change (legSign (flags c i).1 * chosenChartSource c x e (v u) /
    halfJacobian c x i (inverseRoot c x i u)) ^ 2 = _
  change chosenChartSource c x e (v u) ^ 2 = _ at hs
  rw [div_pow, mul_pow, hl, one_mul, hs, halfJacobian, div_pow,
    (OriginalFourMActualChart.chosen_roots hx hx1 c i).1,
    ← pow_mul, show (3 : ℕ) * 2 = 2 * 3 by decide, pow_mul, inverseRoot_sq]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  change _ = (1 - loweringParameter c i * v u) ^ 3 * _
  ring

private def physicalPoint (x : ℂ) : Puncture → ℂ → ℂ
  | .P, u => 1 + u
  | .Q, u => x + u
  | .R, u => u
  | .S, u => u⁻¹

/-- The squared source has the common physical quartic denominator with the
local branch factor removed at the chosen puncture. -/
private def sourceDenominator (x : ℂ) : Puncture → ℂ → ℂ
  | .P, u => (1 + u) * (1 + u - x)
  | .Q, u => (x + u) * (x + u - 1)
  | .R, u => (u - 1) * (u - x)
  | .S, u => (1 - u) * (1 - x * u)

private theorem physicalSource_sq_common {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) :
    (fun u => physicalSource c x i u ^ 2) =ᶠ[𝓝 (0 : ℂ)]
      (fun u => (chartScale c x) ^ 2 * (x : ℂ) / sourceDenominator x i u) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hx1' : (x : ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  have h1x : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr hx1'.symm
  have hnx1 : -1 + (x : ℂ) ≠ 0 := by simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hx1'
  have hr := OriginalFourMActualChart.chosen_roots hx hx1 .B .Q
  have hsq : (Real.sqrt x : ℂ) ^ 2 = x := hr.1
  have hb : (-I * (Real.sqrt x : ℂ)) ^ 2 = -(x : ℂ) := by
    rw [mul_pow, neg_sq, Complex.I_sq, hsq, neg_one_mul]
  have hdsq : I⁻¹ ^ 2 = (-1 : ℂ) := by rw [inv_pow, Complex.I_sq]; norm_num
  have hlocal : ∀ᶠ u : ℂ in 𝓝 0, scale c (x : ℂ) i + loweringParameter c i * u ≠ 0 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually_ne
      (by simpa using scale_ne hx hx1 c i)
  have hden : ∀ᶠ u : ℂ in 𝓝 0, sourceDenominator x i u ≠ 0 := by
    have hcont : Continuous (sourceDenominator x i) := by
      cases i <;> unfold sourceDenominator <;> fun_prop
    exact hcont.continuousAt.eventually_ne (by
      cases i <;> simp [sourceDenominator, hx0, h1x, sub_ne_zero.mpr hx1'])
  have hrb : ContinuousAt (fun u => b (rawLocal c x i u)) 0 :=
    continuousAt_const.sub (rawLocal_analytic hx hx1 c i).continuousAt
  have hrh : ContinuousAt (fun u => h (flags c i).2 (rawLocal c x i u) (parameter c x)) 0 := by
    generalize (flags c i).2 = e
    cases e <;> simp only [h, Bool.false_eq_true, ite_false, ite_true]
    · exact continuousAt_const.sub (rawLocal_analytic hx hx1 c i).continuousAt
    · exact continuousAt_const.sub (continuousAt_const.mul (rawLocal_analytic hx hx1 c i).continuousAt)
  have hrv : h (flags c i).2 (rawLocal c x i 0) (parameter c x) ≠ 0 := by
    cases (flags c i).2 <;> simp [h, rawLocal, chart_parameter_ne_one hx hx1 c]
  filter_upwards [physicalSource_sq hx hx1 c i, hlocal, hden,
    hrb.eventually_ne (y := (0 : ℂ)) (by simp [b, rawLocal]), hrh.eventually_ne hrv]
    with u hu hlocal hden hrb hrh
  rw [hu]
  dsimp only
  rw [div_eq_div_iff (mul_ne_zero (scale_ne hx hx1 c i) (mul_ne_zero hrb hrh)) hden]
  cases c <;> cases i <;>
    simp only [rawLocal, scale, loweringParameter, parameter, flags, b, h, Bool.false_eq_true,
      ite_false, ite_true, zero_mul, one_mul, add_zero, sub_zero, sub_sub_cancel, chartScale,
      sourceDenominator, bLift, inv_pow, hb, hdsq, one_pow] at hlocal ⊢ <;>
    field_simp [hx0, h1x, hnx1, hlocal] <;> try ring
  have hd : (-1 : ℂ) + u * (x : ℂ) ≠ 0 := by
    intro he
    apply hlocal
    apply mul_right_cancel₀ hx0
    rw [zero_mul, add_mul, neg_mul, inv_mul_cancel₀ hx0]
    exact he
  field_simp [hd]
  ring

/-- Transport of the actual signed half-current sources at all physical
punctures as germs. The reversed detector and the two D signs are kept. -/
theorem signed_physical_source_transport {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (i : Puncture) :
    (fun u => chartScale .B x * physicalSource .A x i u) =ᶠ[𝓝 (0 : ℂ)]
      (fun u => relativeB i * physicalSource .B x i u) ∧
    (fun u => chartScale .D x * physicalSource .A x i u) =ᶠ[𝓝 (0 : ℂ)]
      (fun u => relativeD i * physicalSource .D x i u) := by
  have hsign := OriginalFourMChartProduct.physical_source_signs hx hx1
    (flags .A i).1 (flags .A i).2 (flags .B i).1 (flags .B i).2
    (flags .D i).1 (flags .D i).2 (by simp only [chartPuncture_flags])
    (by simp only [chartPuncture_flags])
  dsimp only at hsign
  simp only [chartPuncture_flags] at hsign
  have hsrc (c : Chart) : physicalSource c x i 0 ≠ 0 := by
    rw [physicalSource_zero hx hx1]
    have hroot := root_ne hx hx1 c i
    have hp : periodRoot c x ≠ 0 := by
      intro hz
      have hp : periodRoot c x ^ 2 = 1 - parameter c (x : ℂ) :=
        (OriginalFourMActualChart.chosen_roots hx hx1 c i).2
      exact chart_parameter_ne_one hx hx1 c (by simpa [hz] using hp.symm)
    cases c <;> cases i <;>
      simp_all [halfDifferentialAt, rightSign, outgoing]
  have step (c : Chart) (s : ℂ) (hs : s ^ 2 = 1)
      (h₀ : chartScale c x * halfDifferentialAt .A x i = s * halfDifferentialAt c x i) :
      (fun u => chartScale c x * physicalSource .A x i u) =ᶠ[𝓝 (0 : ℂ)]
        (fun u => s * physicalSource c x i u) := by
    have hs₀ : s ≠ 0 := fun h => by simp [h] at hs
    have hne : chartScale c x * physicalSource .A x i 0 +
        s * physicalSource c x i 0 ≠ 0 := by
      rw [physicalSource_zero hx hx1, physicalSource_zero hx hx1, h₀, ←
        physicalSource_zero hx hx1 c i, ← two_mul]
      exact mul_ne_zero (by norm_num) (mul_ne_zero hs₀ (hsrc c))
    have hcont : ContinuousAt (fun u => chartScale c x * physicalSource .A x i u +
        s * physicalSource c x i u) 0 :=
      (continuousAt_const.mul (physicalSource_analytic hx hx1 .A i).continuousAt).add
        (continuousAt_const.mul (physicalSource_analytic hx hx1 c i).continuousAt)
    filter_upwards [physicalSource_sq_common hx hx1 .A i, physicalSource_sq_common hx hx1 c i,
      hcont.eventually_ne (y := (0 : ℂ)) hne] with u hA hC hsum
    have he : (chartScale c x * physicalSource .A x i u) ^ 2 =
        (s * physicalSource c x i u) ^ 2 := by
      rw [mul_pow, mul_pow, hs, one_mul, hA, hC, show chartScale .A x = 1 by rfl, one_pow]
      ring
    have hprod : (chartScale c x * physicalSource .A x i u +
          s * physicalSource c x i u) *
        (chartScale c x * physicalSource .A x i u -
          s * physicalSource c x i u) = 0 := by
      rw [← sq_sub_sq, he, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hsum)
  exact ⟨step .B _ (by cases i <;> norm_num [relativeB]) hsign.1,
    step .D _ (by cases i <;> norm_num [relativeD]) hsign.2⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMOccupationTransport
