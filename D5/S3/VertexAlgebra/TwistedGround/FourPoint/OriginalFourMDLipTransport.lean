/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original D-boundary Taylor entries in the common four-point coordinates. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChartSource
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccupation

/-! The common spatial coordinates pull back the actual D-boundary
Gaussian entries by the same finite creator transforms as the radial charts. -/

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalFourMActualChart (Chart Puncture parameter scaleRoot loweringParameter)
open OriginalFourMOccupationTransport (flags physicalSource)
open OriginalFourMPhysicalCovariance (physicalCovariance)
open OriginalFourMCauchyTaylor (selected_physical_covariance)
open OriginalFourMSignedOverlap (legSign chosen_chart_source_analytic taggedMode)
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalGaussianExternalBlocks (External)
open OriginalFourMSlitMean (slitCovarianceEntry slitCovarianceEntry_analyticOnNhd
  slitCovarianceEntry_eq_native)
open OriginalFourMPeriodSource (dLip)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitDomain)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport (contractionScalar)
open private chosenChartSource from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open private rawLocal chartPeriod from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private inverseJac creatorEntry inverse_pullback_entry coefficient_mul_scalar from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open private explicit_covariance_symmetric from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccupation
open private slitDomain_star midpoint_mem mem_slitDomain from
  D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open private dLip_neBot dLip_im_ne_zero mem_doubleSlit_of_im from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource

private theorem slit_covariance_entry_swap (D : LatticeData) (l k : Bool) (x y : External D)
    {r : ℂ} (hr : r ∈ slitDomain) :
    slitCovarianceEntry D l k x y r = slitCovarianceEntry D k l y x r := by
  refine (slitCovarianceEntry_analyticOnNhd D l k x y).eqOn_of_preconnected_of_eventuallyEq
    (slitCovarianceEntry_analyticOnNhd D k l y x)
    (slitDomain_star.isPathConnected midpoint_mem.1).isConnected.isPreconnected
    (z₀ := (0 : ℂ)) ((mem_slitDomain _).2 (Or.inl (by norm_num))) ?_ hr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with s hs
  let w := s ^ (1 / 2 : ℂ)
  have hw2 : w ^ 2 = s := by
    unfold w
    rw [← Complex.cpow_mul_nat]
    norm_num
  have hw : ‖w‖ < 1 := by
    have h : ‖w ^ 2‖ < 1 := by
      rw [hw2]
      simpa [Metric.mem_ball] using hs
    rw [norm_pow] at h
    nlinarith [norm_nonneg w]
  rw [← hw2]
  exact (slitCovarianceEntry_eq_native D id l k x y hw).trans
    ((explicit_covariance_symmetric D id hw (taggedMode l x) (taggedMode k y)).trans
      (slitCovarianceEntry_eq_native D id k l y x hw).symm)

/-- The signed Taylor matrix stays symmetric on the actual D boundary. -/
theorem dLip_covariance_entry_swap (D : LatticeData) (upperA l k : Bool)
    (x y : External D) {t : ℝ} (ht : 1 < t) :
    dLipCovarianceEntry D upperA l k x y (t : ℂ) =
      dLipCovarianceEntry D upperA k l y x (t : ℂ) := by
  let F := 𝓝[dLip upperA] (t : ℂ)
  have : F.NeBot := dLip_neBot upperA t
  have hl := (dLipCovarianceEntry_analyticAt D upperA l k x y ht).continuousAt
  have hk := (dLipCovarianceEntry_analyticAt D upperA k l y x ht).continuousAt
  have hF : F ≤ 𝓝 (t : ℂ) := nhdsWithin_le_nhds
  refine tendsto_nhds_unique_of_eventuallyEq (hl.tendsto.mono_left hF) (hk.tendsto.mono_left hF) ?_
  filter_upwards [self_mem_nhdsWithin (s := dLip upperA) (a := (t : ℂ))] with u hu
  rw [dLipCovarianceEntry_eq_slit D upperA l k x y hu,
    dLipCovarianceEntry_eq_slit D upperA k l y x hu]
  exact slit_covariance_entry_swap D l k x y (mem_doubleSlit_of_im (dLip_im_ne_zero hu)).1

/-- The physical D mean selects the actual lip entries after the finite
inverse coordinate transform. -/
theorem selected_dLip_physical_mean (D : LatticeData) (q : Charge D)
    {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) (i : Puncture) (x : Index D) :
    coefficient x.2 (fun u =>
      -(bilinear D (unitCharge D x.1) q : ℂ) *
        physicalSource .D z i u / chartPeriod true .D z) =
      ∑ k ∈ Finset.range (x.2 + 1), creatorEntry .D z i x.2 k *
        ((bilinear D (unitCharge D x.1) q : ℂ) *
          dLipMeanEntry true (flags .D i).1 (flags .D i).2 k (parameter .D (z : ℂ))) := by
  let f : ℂ → ℂ := fun v => -legSign (flags .D i).1 *
    chosenChartSource .D z (flags .D i).2 v / chartPeriod true .D z
  let a : ℂ := bilinear D (unitCharge D x.1) q
  have hf : AnalyticAt ℂ f 0 := (analyticAt_const.mul
    (chosen_chart_source_analytic hz hz₁ .D (flags .D i).2)).div_const
  have hp : (fun u => -a * physicalSource .D z i u / chartPeriod true .D z) =
      fun u => inverseJac .D z i u * (a * f (rawLocal .D z i u)) := by
    funext u
    simp only [physicalSource, inverseJac, f, div_eq_mul_inv]
    ring
  change coefficient x.2 (fun u => -a * physicalSource .D z i u / chartPeriod true .D z) = _
  rw [hp]
  have he : AnalyticAt ℂ (fun v => a * f v) 0 := analyticAt_const.mul hf
  rw [inverse_pullback_entry hz hz₁ .D i he]
  apply Finset.sum_congr rfl
  intro k _
  rw [coefficient_mul_scalar, dLipMeanEntry_eq_chart hz hz₁]

/-- The two-leg selector in physical D coordinates uses the actual D-lip
covariance, including the same-puncture contraction. -/
theorem selected_dLip_physical_covariance (D : LatticeData) (hu : IsUnit D.G.det)
    {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) (i j : Puncture) (x y : Index D) :
    (D.G x.1 y.1 : ℂ) * coefficient y.2 (fun v => coefficient x.2 (fun u =>
      physicalCovariance true .D z i j u v)) =
      (∑ k ∈ Finset.range (x.2 + 1), ∑ l ∈ Finset.range (y.2 + 1),
        creatorEntry .D z i x.2 k * creatorEntry .D z j y.2 l *
          dLipCovarianceEntry D true (flags .D i).1 (flags .D j).1
            ((flags .D i).2, x.1, k) ((flags .D j).2, y.1, l) (parameter .D (z : ℂ))) +
      (if (flags .D i).1 = (flags .D j).1 ∧ (flags .D i).2 = (flags .D j).2 then
        ((scaleRoot .D z i)⁻¹)^(2*x.2+1) * ((scaleRoot .D z i)⁻¹)^(2*y.2+1) *
          ((D.G x.1 y.1 : ℂ) * ((-loweringParameter .D i)^(x.2+y.2+1) *
            contractionScalar x.2 y.2))
      else 0) := by
  rw [selected_physical_covariance D hu hz hz₁ true .D i j x y]
  dsimp only
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [dLipCovarianceEntry_eq_chart D hz hz₁]
  simp only [coefficient_mul_scalar]
  change _ * (_ * _ * _) = _ * _ * ((D.G x.1 y.1 : ℂ) * _)
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
