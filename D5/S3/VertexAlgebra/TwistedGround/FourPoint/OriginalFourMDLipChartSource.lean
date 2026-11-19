/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChartSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChartSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identification of the original radial and D-boundary Gaussian chart data. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipSector
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct

/-! Identification of the local D continuation with its chosen radial source. -/

open Complex Filter
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open OriginalFourMActualChart (Chart parameter periodRoot)
open LatticeGeneratingFieldLocality (LatticeData Charge bilinear unitCharge)
open OriginalGaussianExternalBlocks (External)
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalGaussianExternalAnalyticCandidate (b)
open OriginalGaussianExternalSignedCandidate (h)
open OriginalFourMSlitMean (slitMean)
open OriginalFourMSignedOverlap (chartCovariance legSign)
open OriginalFourMPeriodSource (chartCorrection dPeriod)
open OriginalFourMDLipNome (dNome dTau)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod slitPeriod_ne_zero tau)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (doubleSlit)
open D5.S3.Analytic.OriginalHalfBinomialDiskCorrection (disk)
open D5.S3.Analytic.OriginalHalfBinomialNome (Q0)
open D5.S3.Analytic.OriginalHalfBinomialPfaffNome (negativeChartNome)
open D5.S3.Analytic.OriginalSlitNome (slitNome slitNome_eq_Q0 slitNome_eq_exp)
open private normalizedBranch chosenChartSource normalizedBranch_zero normalizedBranch_analytic
  chart_parameter_ne_one chartW from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open private phase from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipMean
open private dW dCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipCovariance
open private rootB rootZ from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart
open private chartPeriod chartTau from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private lipSign chartA_mem doubleSlit_of_re pfaffMap_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
open private nomeOffZero from D5.S3.Analytic.OriginalSlitNome
open private coefficient_congr from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitTaylor

private theorem ofReal_mul_cpow_positive {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ≠ 0)
    (p : ℂ) : ((a : ℂ) * z) ^ p = (a : ℂ) ^ p * z ^ p := by
  have hn : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hn hz), cpow_def_of_ne_zero hn, cpow_def_of_ne_zero hz,
    Complex.log_ofReal_mul ha hz, Complex.ofReal_log ha.le, add_mul, exp_add]

private theorem dPeriodRoot_eq (z : ℝ) (hz : 0 < z) (hz₁ : z < 1) :
    periodRoot .D z = I * (Real.sqrt (z⁻¹ - 1) : ℂ) := by
  have he : z⁻¹ - 1 = (1 - z) / z := by field_simp [hz.ne']
  rw [he, Real.sqrt_div (sub_nonneg.mpr hz₁.le), ofReal_div]
  simp only [periodRoot, rootB, rootZ, mul_div_assoc]

/-- On the matched D boundary the local inverse-half-power continuation is
the exact source used in the physical chart. -/
theorem dLipMean_eq_chosenChartSource {z : ℝ} (hz : 0 < z) (hz₁ : z < 1)
    (e : Bool) {u : ℂ} (hb : b u ≠ 0)
    (hbr : normalizedBranch e u (parameter .D (z : ℂ)) ≠ 0) :
    dLipMean true e u (parameter .D (z : ℂ)) = chosenChartSource .D z e u := by
  cases e
  · let a : ℝ := z⁻¹ - 1
    let r : ℂ := parameter .D (z : ℂ)
    have ha : 0 < a := sub_pos.mpr ((one_lt_inv₀ hz).2 hz₁)
    have hr : 1 - r = -(a : ℂ) := by
      simp only [r, parameter, a, ofReal_sub, ofReal_inv, ofReal_one]
      ring
    have hn : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
    have harg : -(h false u r / b u) =
        (a : ℂ) * normalizedBranch false u (parameter .D (z : ℂ)) := by
      change -(h false u r / b u) = (a : ℂ) * normalizedBranch false u r
      simp only [normalizedBranch, Bool.false_eq_true, ite_false, hr]
      field_simp [hb, hn]
    have hphase : (-I) * (a : ℂ) ^ (-1 / 2 : ℂ) = (periodRoot .D z)⁻¹ := by
      rw [dPeriodRoot_eq z hz hz₁, mul_inv_rev, inv_I]
      have he : (a : ℂ) ^ (-1 / 2 : ℂ) = ((Real.sqrt a : ℂ))⁻¹ := by
        rw [show (-1 / 2 : ℂ) = - (1 / 2 : ℂ) by norm_num, cpow_neg,
          Real.sqrt_eq_rpow, ofReal_cpow ha.le]
        norm_num
      rw [he, mul_comm]
    change dLipMean true false u r = chosenChartSource .D z false u
    simp only [dLipMean, Bool.false_eq_true, ite_false, phase, ite_true, chosenChartSource,
      one_div, mul_inv_rev]
    rw [harg, ofReal_mul_cpow_positive ha hbr, ← mul_assoc (-I), hphase]
    ring
  · simp [dLipMean, slitMean, chosenChartSource, normalizedBranch, one_div]

theorem dLipMean_radial_germ {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) (e : Bool) :
    (fun u => dLipMean true e u (parameter .D (z : ℂ))) =ᶠ[𝓝 0] chosenChartSource .D z e := by
  have hb : ∀ᶠ u : ℂ in 𝓝 0, b u ≠ 0 :=
    (show ContinuousAt b 0 by unfold b; fun_prop).eventually_ne (by simp [b])
  have ht := chart_parameter_ne_one hz hz₁ .D
  have hbranch : ∀ᶠ u : ℂ in 𝓝 0, normalizedBranch e u (parameter .D (z : ℂ)) ≠ 0 :=
    (normalizedBranch_analytic e ht).continuousAt.eventually_ne
      (by rw [normalizedBranch_zero e ht]; exact one_ne_zero)
  filter_upwards [hb, hbranch] with u hu hv
  exact dLipMean_eq_chosenChartSource hz hz₁ e hu hv

/-- The signed covariance agrees on the original spatial germ of the physical D chart. -/
theorem dLipCovariance_radial_germ {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) (l k e f : Bool) :
    ∀ᶠ v : ℂ in 𝓝 0, ∀ᶠ u : ℂ in 𝓝 0,
      dLipCovariance true l k e f u v (parameter .D (z : ℂ)) =
        chartCovariance true .D z l k e f u v := by
  filter_upwards [dLipMean_radial_germ hz hz₁ f] with v hv
  filter_upwards [dLipMean_radial_germ hz hz₁ e] with u hu
  change dLipMean true f v (parameter .D (z : ℂ)) = chosenChartSource .D z f v at hv
  change dLipMean true e u (parameter .D (z : ℂ)) = chosenChartSource .D z e u at hu
  simp only [dLipCovariance, chartCovariance, dW, chartW, dCorrection, chartCorrection, hu, hv]

private theorem chart_tau_A {z : ℝ} (hz : 0 < z) (upperA : Bool) :
    chartTau upperA .A z = tau (1 - (z : ℂ)) + lipSign upperA := by
  have hP := slitPeriod_ne_zero (chartA_mem hz)
  change I * dPeriod upperA (parameter .D (z : ℂ)) / slitPeriod (parameter .A (z : ℂ)) = _
  rw [dPeriod, show 1 - (parameter .D (z : ℂ))⁻¹ = 1 - (z : ℂ) by simp [parameter],
    show 1 - parameter .D (z : ℂ) = parameter .A (z : ℂ) from rfl]
  field_simp [I_ne_zero, hP]

/-- The continued nome on the D lip is the nome in the physical charge sum. -/
theorem dLipNome_eq_chart {z : ℝ} (hz : 0 < z) (upperA : Bool) :
    dNome upperA (parameter .D (z : ℂ)) =
      Complex.exp ((Real.pi : ℂ) * I * chartTau upperA .D z) := by
  have hTau : dTau upperA (parameter .D (z : ℂ)) = chartTau upperA .D z := by
    change dTau upperA (parameter .D (z : ℂ)) = -1 / chartTau upperA .A z
    simp only [dTau, parameter, inv_inv, neg_div, one_div, chart_tau_A hz]
  rw [dNome, hTau, mul_comm I]

/-- The two radial charge sums use the original nome, including the
negative-real Pfaff sign in A and the complementary period ratio in B. -/
theorem radial_nome_eq_chart {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) (upperA : Bool)
    (c : Chart) (hc : c = .A ∨ c = .B) (hDisk : parameter c (z : ℂ) ∈ disk) :
    Complex.exp ((Real.pi : ℂ) * I * chartTau upperA c z) = Q0 (parameter c (z : ℂ)) := by
  rw [← slitNome_eq_Q0 hDisk]
  rcases hc with rfl | rfl
  · let r := parameter .A (z : ℂ)
    have hr : r.re < 0 := by
      change (1 - (z : ℂ)⁻¹).re < 0
      simp only [← ofReal_inv, sub_re, one_re, ofReal_re]
      linarith [(one_lt_inv₀ hz).2 hz₁]
    have hi : r.im = 0 := by simp [r, parameter, ← ofReal_inv]
    have hn : r ≠ 0 := fun h => hr.ne (by rw [h, zero_re])
    have hs : r ∉ doubleSlit := fun h =>
      (mem_slitPlane_iff.mp h.2).elim (not_lt_of_ge hr.le) (fun hp => hp hi)
    have hpf : r / (r - 1) = 1 - (z : ℂ) := by
      have h₀ : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
      simpa only [r, parameter, inv_inv] using pfaffMap_eq ((z : ℂ)⁻¹) (inv_ne_zero h₀)
    have hsign : Complex.exp ((Real.pi : ℂ) * I * lipSign upperA) = -1 := by
      cases upperA
      · rw [show lipSign false = -1 by rfl, mul_neg_one, Complex.exp_neg_pi_mul_I]
      · rw [show lipSign true = 1 by rfl, mul_one, Complex.exp_pi_mul_I]
    change Complex.exp ((Real.pi : ℂ) * I * chartTau upperA .A z) = slitNome r
    rw [slitNome, ite_eq_right hn, nomeOffZero, ite_eq_right hs, negativeChartNome, hpf,
      chart_tau_A hz, mul_add, Complex.exp_add, hsign, mul_neg_one, mul_comm I]
  · have hs : (z : ℂ) ∈ doubleSlit := doubleSlit_of_re (by simpa using hz) (by simpa using hz₁)
    have he : chartTau upperA .B z = tau (z : ℂ) := by
      change -1 / (I * slitPeriod (z : ℂ) / slitPeriod (1 - (z : ℂ))) = _
      rw [tau, neg_div, one_div, inv_div]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_I]
      ring
    rw [parameter, slitNome_eq_exp hs, he, mul_comm I]

/-- The D-boundary mean selector is the Taylor coefficient of the actual
period-normalized chart source. -/
theorem dLipMeanEntry_eq_chart {z : ℝ} (hz : 0 < z) (hz₁ : z < 1)
    (l e : Bool) (p : ℕ) :
    dLipMeanEntry true l e p (parameter .D (z : ℂ)) =
      coefficient p (fun u => -legSign l * chosenChartSource .D z e u / chartPeriod true .D z) := by
  unfold dLipMeanEntry
  apply coefficient_congr
  exact (dLipMean_radial_germ hz hz₁ e).mono fun u hu => by
    change dLipMean true e u (parameter .D (z : ℂ)) = chosenChartSource .D z e u at hu
    exact congrArg (fun a => -legSign l * a / dPeriod true (parameter .D (z : ℂ))) hu

/-- The D-boundary covariance selector retains both original spatial
indices and the Gram entry in the actual chart. -/
theorem dLipCovarianceEntry_eq_chart (D : LatticeData) {z : ℝ}
    (hz : 0 < z) (hz₁ : z < 1) (l k : Bool) (x y : External D) :
    dLipCovarianceEntry D true l k x y (parameter .D (z : ℂ)) =
      coefficient y.2.2 (fun v => coefficient x.2.2 (fun u =>
        (D.G x.2.1 y.2.1 : ℂ) * chartCovariance true .D z l k x.1 y.1 u v)) := by
  unfold dLipCovarianceEntry
  apply coefficient_congr
  filter_upwards [dLipCovariance_radial_germ hz hz₁ l k x.1 y.1] with v hv
  apply coefficient_congr
  exact hv.mono fun _ h => congrArg ((D.G x.2.1 y.2.1 : ℂ) * ·) h

open LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open OriginalFourMChargeNormal OriginalChargedRowSource OriginalGaussianSourceRestriction
open OriginalFourMSectorContinuation
open private leg from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation
open private dDeterminant dMatrix dLinear from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipSector

private theorem dLip_charge_factor_eq_chart (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (q : Charge D)
    {z : ℝ} (hz : 0 < z) (upperA : Bool) :
    dNome upperA (parameter .D (z : ℂ)) ^ (chargeEnergy D q).toNat =
      Complex.exp ((Real.pi : ℂ) * I * chartTau upperA .D z * (bilinear D q q : ℂ) / 2) := by
  let m := (chargeEnergy D q).toNat
  have hm : (m : ℤ) = chargeEnergy D q := Int.toNat_of_nonneg (chargeEnergy_nonneg D hD q)
  have hq : (bilinear D q q : ℂ) = 2 * (m : ℂ) := by
    have he : bilinear D q q = 2 * (m : ℤ) := by rw [hm, two_chargeEnergy]
    exact_mod_cast he
  rw [dLipNome_eq_chart hz, ← Complex.exp_nat_mul, hq]
  congr 1
  ring

/-- Multiplication by the original cubic factor identifies the D-lip
sector with the period-normalized finite-occupation charge sum in chart D. -/
theorem dLipChargeSector_normalized (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : ModTwoCharge D)
    (betaL gammaL betaR gammaR : Exponent D) {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) :
    let F := fourSupport D betaL gammaL betaR gammaR
    let label := Sum.elim (compactExternal D F) (compactExternal D F)
    let A := fun i j => coefficient (label j).2.2 (fun v =>
      coefficient (label i).2.2 (fun u => (D.G (label i).2.1 (label j).2.1 : ℂ) *
        chartCovariance true .D z (leg i) (leg j) (label i).1 (label j).1 u v))
    let M := fun (q : Charge D) i => (bilinear D (unitCharge D (label i).2.1) q : ℂ) *
      coefficient (label i).2.2 (fun u =>
        -legSign (leg i) * chosenChartSource .D z (label i).1 u / chartPeriod true .D z)
    let r := parameter .D (z : ℂ)
    (1 - r) ^ (3 : ℕ) * dLipChargeSector D true a betaL gammaL betaR gammaR r =
      ∑' q : Charge D, if reduceCharge D q = a then
        (chartPeriod true .D z ^ (12 : ℕ))⁻¹ *
          Complex.exp ((Real.pi : ℂ) * I * chartTau true .D z * (bilinear D q q : ℂ) / 2) *
          affineCoefficient A (M q) (externalOccupation D F betaL gammaL betaR gammaR)
      else 0 := by
  classical
  dsimp only
  have hne : 1 - parameter .D (z : ℂ) ≠ 0 := by
    have hlt : 1 < z⁻¹ := (one_lt_inv₀ hz).2 hz₁
    apply sub_ne_zero.mpr
    rw [parameter, ← ofReal_inv, ← ofReal_one]
    exact_mod_cast hlt.ne
  unfold dLipChargeSector
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  by_cases hq : reduceCharge D q = a
  · simp only [hq, ite_true]
    rw [dLip_charge_factor_eq_chart D hD q hz]
    simp only [dLinear, dLipMeanEntry_eq_chart hz hz₁]
    rw [dDeterminant]
    change _ = ((dPeriod true (parameter .D (z : ℂ))) ^ (12 : ℕ))⁻¹ * _ * _
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hne), one_mul]
    let e := compactExternal D (fourSupport D betaL gammaL betaR gammaR)
    have hA (i j : _ ⊕ _) :
        dMatrix D true e (parameter .D (z : ℂ)) i j = _ :=
      dLipCovarianceEntry_eq_chart D hz hz₁ (leg i) (leg j) (Sum.elim e e i) (Sum.elim e e j)
    rw [funext fun i => funext (hA i)]
  · simp [hq]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
