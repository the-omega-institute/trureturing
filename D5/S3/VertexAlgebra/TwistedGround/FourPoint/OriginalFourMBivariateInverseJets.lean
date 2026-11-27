/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMBivariateInverseJets
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMBivariateInverseJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent inverse jet substitution at the two endpoints of a native pair. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCorrectionJets

/-! An analytic native pair admits finite Taylor substitution in both
physical coordinates, with the chosen half-Jacobian on each endpoint. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInverseJets

open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (rawLocal inverseRoot inverseRoot_analytic inverseRoot_zero
  rawLocal_analytic root_ne halfJacobian)
open OriginalFourMPhysicalCovariance (jac)
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalFourMSlitMean (analytic_coefficient_slice coefficient_congr)

/-- The native-mode coefficient of one inverse jet, including the inverse
root and the full inverse spatial scale. -/
def inverseJetWeight (c : Chart) (x : ℝ) (i : Puncture) (m n : ℕ) : ℂ :=
  (scaleRoot c x i)⁻¹ * ((scale c x i)⁻¹) ^ m *
    (-loweringParameter c i) ^ (m - n) * Ring.choose ((m : ℂ) + 1 / 2) (m - n)

/-- Substitution in the two coordinates acts by the product of the two
finite inverse jet weights, with both requested degrees arbitrary. -/
theorem coefficient_comp_pair_div_jac {f : ℂ × ℂ → ℂ} (hf : AnalyticAt ℂ f (0, 0))
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (c : Chart) (i j : Puncture) (p q : ℕ) :
    coefficient q (fun v => coefficient p (fun u =>
      f (rawLocal c x i u, rawLocal c x j v) / (jac c x i u * jac c x j v))) =
      ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (q + 1),
        coefficient b (fun v => coefficient a (fun u => f (u, v))) *
          inverseJetWeight c x i p a * inverseJetWeight c x j q b := by
  let L := rawLocal c x j
  let s (a : ℕ) (v : ℂ) := coefficient a (fun u => f (u, v))
  let w := inverseJetWeight c x i p
  have hJ : AnalyticAt ℂ (jac c x j) 0 :=
    analyticAt_const.div ((inverseRoot_analytic hx hx₁ c j).pow 3) (by simp [inverseRoot_zero])
  have hJ₀ : jac c x j 0 ≠ 0 := by simp [jac, halfJacobian, inverseRoot_zero, root_ne hx hx₁]
  have hL : AnalyticAt ℂ L 0 := rawLocal_analytic hx hx₁ c j
  have hL₀ : L 0 = 0 := by simp [L, rawLocal]
  have hS (a : ℕ) : AnalyticAt ℂ (s a) 0 := analytic_coefficient_slice hf a
  have hcomp (a : ℕ) : AnalyticAt ℂ (fun v => s a (L v) / jac c x j v * w a) 0 :=
    (((hS a).comp_of_eq hL hL₀).div hJ hJ₀).mul analyticAt_const
  have hv : ContinuousAt (fun v : ℂ => ((0 : ℂ), L v)) 0 :=
    continuousAt_const.prodMk hL.continuousAt
  have hnear : ∀ᶠ v : ℂ in 𝓝 0, AnalyticAt ℂ f (0, L v) :=
    hv.eventually (by simpa only [hL₀] using hf.eventually_analyticAt)
  have he :
      (fun v => coefficient p (fun u =>
        f (rawLocal c x i u, L v) / (jac c x i u * jac c x j v))) =ᶠ[𝓝 0]
      fun v => ∑ a ∈ Finset.range (p + 1), s a (L v) / jac c x j v * w a := by
    filter_upwards [hnear] with v hv
    have ha : AnalyticAt ℂ (fun u : ℂ => f (u, L v)) 0 :=
      hv.fun_comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    have hh := coefficient_comp_rawLocal_div_halfJacobian ha hx hx₁ c i p
    have hsplit : (fun u => f (rawLocal c x i u, L v) /
        (jac c x i u * jac c x j v)) =
        fun u => (f (rawLocal c x i u, L v) / jac c x i u) * (jac c x j v)⁻¹ := by
      funext u
      rw [← div_div, div_eq_mul_inv _ (jac c x j v)]
    rw [hsplit, show coefficient p (fun u => (f (rawLocal c x i u, L v) / jac c x i u) *
      (jac c x j v)⁻¹) = coefficient p (fun u => f (rawLocal c x i u, L v) /
      jac c x i u) / jac c x j v by
      simp only [coefficient, iteratedDeriv_mul_const_field, div_eq_mul_inv]
      ring]
    rw [show coefficient p (fun u => f (rawLocal c x i u, L v) / jac c x i u) =
        ∑ a ∈ Finset.range (p + 1), s a (L v) * w a from hh, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  change coefficient q (fun v => coefficient p (fun u =>
    f (rawLocal c x i u, L v) / (jac c x i u * jac c x j v))) = _
  rw [coefficient_congr he]
  have hsum :
      coefficient q (fun v => ∑ a ∈ Finset.range (p + 1), s a (L v) / jac c x j v * w a) =
      ∑ a ∈ Finset.range (p + 1),
        coefficient q (fun v => s a (L v) / jac c x j v * w a) := by
    unfold coefficient
    rw [iteratedDeriv_fun_sum (fun a _ => (hcomp a).contDiffAt), Finset.sum_div]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro a _
  have hconst : coefficient q (fun v => s a (L v) / jac c x j v * w a) =
      coefficient q (fun v => s a (L v) / jac c x j v) * w a := by
    unfold coefficient
    rw [iteratedDeriv_mul_const_field, div_mul_eq_mul_div]
  rw [hconst]
  have hh := coefficient_comp_rawLocal_div_halfJacobian (hS a) hx hx₁ c j q
  change coefficient q (fun v => s a (L v) / jac c x j v) =
      ∑ b ∈ Finset.range (q + 1), coefficient b (s a) * inverseJetWeight c x j q b at hh
  rw [hh, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  change coefficient b (s a) * inverseJetWeight c x j q b * w a =
    coefficient b (s a) * w a * inverseJetWeight c x j q b
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInverseJets
