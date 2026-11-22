/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Real-regular meromorphic continuation of the complete Mangoldt transform. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
import D5.S3.Weil.Mertens.CriticalThetaTailPeak

/-! The normalized zeta numerator removes the apparent pole at one. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter
open scoped Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular

private def numerator (s : ℂ) : ℂ :=
  (((1 + (Real.eulerMascheroniConstant : ℂ)) * s - 1) * riemannZeta₁ s) -
    deriv riemannZeta₁ s

private def dividedNumerator (s : ℂ) : ℂ :=
  if s = 1 then deriv numerator 1 else numerator s / (s - 1)

/-- The normalized zeta expression with the removable singularity at one filled
by the derivative of the vanishing numerator. -/
def continued (s : ℂ) : ℂ :=
  dividedNumerator s / (s * riemannZeta₁ s)

private theorem numerator_analytic (s : ℂ) : AnalyticAt ℂ numerator s := by
  have hZ := differentiable_riemannZeta₁.analyticAt s
  have hlinear : AnalyticAt ℂ
      (fun z : ℂ => (1 + (Real.eulerMascheroniConstant : ℂ)) * z - 1) s :=
    (analyticAt_const.mul analyticAt_id).sub analyticAt_const
  exact (hlinear.mul hZ).sub hZ.deriv

private theorem numerator_one : numerator 1 = 0 := by
  rw [numerator, riemannZeta₁_one, deriv_riemannZeta₁_one]
  ring

private theorem dividedNumerator_analytic (s : ℂ) : AnalyticAt ℂ dividedNumerator s := by
  by_cases hs : s = 1
  · subst s
    have horder : (1 : ENat) ≤ analyticOrderAt numerator (1 : ℂ) :=
      Order.one_le_iff_ne_zero.mpr ((numerator_analytic 1).analyticOrderAt_ne_zero.mpr
        numerator_one)
    obtain ⟨H, hH, hfactor⟩ :=
      (natCast_le_analyticOrderAt (numerator_analytic 1) (n := 1)).mp
        (by simpa only [Nat.cast_one] using horder)
    have hmul : numerator =ᶠ[𝓝 (1 : ℂ)] fun z => (z - 1) * H z := by
      filter_upwards [hfactor] with z hz
      simpa only [pow_one, smul_eq_mul] using hz
    have hderiv : HasDerivAt (fun z : ℂ => (z - 1) * H z) (H 1) 1 := by
      simpa only [sub_self, zero_mul, one_mul, add_zero] using
        ((hasDerivAt_id' (1 : ℂ)).sub_const (1 : ℂ)).fun_mul hH.differentiableAt.hasDerivAt
    have hvalue : deriv numerator 1 = H 1 := hmul.deriv_eq.trans hderiv.deriv
    apply hH.congr
    filter_upwards [hmul] with z hz
    by_cases hz1 : z = 1
    · subst z
      rw [dividedNumerator, ite_eq_left rfl, hvalue]
    · rw [dividedNumerator, ite_eq_right hz1]
      exact (eq_div_iff (sub_ne_zero.mpr hz1)).mpr (by rw [hz, mul_comm])
  · have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
      analyticAt_id.sub analyticAt_const
    apply ((numerator_analytic s).div hshift (sub_ne_zero.mpr hs)).congr
    filter_upwards [continuousAt_id.eventually_ne hs] with z hz
    change z ≠ 1 at hz
    change numerator z / (z - 1) = dividedNumerator z
    rw [dividedNumerator, ite_eq_right hz]

private theorem continued_eq_transform {s : ℂ} (hs : 1 < s.re) :
    continued s = CompleteMangoldtLaurent.transform s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hZ : riemannZeta₁ s ≠ 0 := by
    intro hz
    apply riemannZeta_ne_zero_of_one_lt_re hs
    rw [riemannZeta_eq_inv_sub_mul hs1, hz, mul_zero]
  have hlog := ThetaLaplaceContinuation.normalized_logDeriv hs1 hZ
  simp only [logDeriv_apply] at hlog
  rw [continued, dividedNumerator, ite_eq_right hs1, numerator, CompleteMangoldtLaurent.transform,
    neg_div, hlog]
  push_cast
  field_simp [hs0, sub_ne_zero.mpr hs1, hZ]
  ring

/-- The complete Mangoldt transform continues meromorphically to the positive
half-plane, holomorphically at each positive real point, and agrees with its
original expression throughout the half-plane of convergence. -/
theorem continuation :
    MeromorphicOn continued {s : ℂ | 0 < s.re} ∧
    (∀ x : ℝ, 0 < x → AnalyticAt ℂ continued (x : ℂ)) ∧
    (∀ s : ℂ, 1 < s.re → continued s = CompleteMangoldtLaurent.transform s) := by
  have hden (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => z * riemannZeta₁ z) s :=
    analyticAt_id.mul (differentiable_riemannZeta₁.analyticAt s)
  refine ⟨fun s _ => ?_, fun x hx => ?_, fun _ hs => continued_eq_transform hs⟩
  · exact (dividedNumerator_analytic s).meromorphicAt.div (hden s).meromorphicAt
  · exact (dividedNumerator_analytic (x : ℂ)).div (hden (x : ℂ))
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')
        (CriticalThetaTailPeak.normalized_zeta_real_ne_zero hx))

#print axioms continuation

end D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtRealRegular
