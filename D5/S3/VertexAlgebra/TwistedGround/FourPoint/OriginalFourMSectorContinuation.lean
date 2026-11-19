/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normal convergence and native agreement of the rank-24 charge-sector terms. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitTaylor
import D5.S3.Analytic.OriginalSlitNome

/-! Normal convergence and native term agreement of the rank-24 charge-sector continuation. -/

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSectorContinuation

set_option maxRecDepth 4096

noncomputable section

open Set Metric
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open OriginalFourMChargeNormal OriginalChargedRowSource OriginalGaussianSourceRestriction
open OriginalFourMEnergyCoefficient OriginalGaussianSewnAnalytic
open private affine_coefficient_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic

/-- The original fixed-occupation coset sum is holomorphic on an open chart
on which the actual Gaussian data are holomorphic and the nome is subunit. -/
theorem charge_sector_differentiableOn (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (betaL gammaL betaR gammaR : Exponent D) (a : ModTwoCharge D)
    (U : Set ℂ) (hU : IsOpen U) (p Q : ℂ → ℂ)
    (hp : DifferentiableOn ℂ p U) (hQ : DifferentiableOn ℂ Q U)
    (hQlt : ∀ z ∈ U, ‖Q z‖ < 1)
    (A : ℂ → Matrix
      (CompactExternal D (fourSupport D betaL gammaL betaR gammaR) ⊕
       CompactExternal D (fourSupport D betaL gammaL betaR gammaR))
      (CompactExternal D (fourSupport D betaL gammaL betaR gammaR) ⊕
       CompactExternal D (fourSupport D betaL gammaL betaR gammaR)) ℂ)
    (u : ℂ → CompactExternal D (fourSupport D betaL gammaL betaR gammaR) ⊕
       CompactExternal D (fourSupport D betaL gammaL betaR gammaR) → ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) U)
    (hu : ∀ i, DifferentiableOn ℂ (fun z => u z i) U) :
    let F := fourSupport D betaL gammaL betaR gammaR
    let d := externalOccupation D F betaL gammaL betaR gammaR
    let label := Sum.elim (compactExternal D F) (compactExternal D F)
    DifferentiableOn ℂ (fun z => ∑' q : Charge D,
      if reduceCharge D q = a then
        p z * Q z ^ (chargeEnergy D q).toNat * affineCoefficient (A z)
          (fun i => (bilinear D (unitCharge D (label i).2.1) q : ℂ) * u z i) d
      else 0) U := by
  classical
  dsimp only
  intro z hz
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let K : Set ℂ := closedBall z (r / 2)
  have hKU : K ⊆ U := (closedBall_subset_ball (by linarith : r / 2 < r)).trans hrU
  obtain ⟨⟨b, hb, hmajor⟩, _⟩ := compact_charge_normal D hD betaL gammaL betaR gammaR
    K (isCompact_closedBall _ _) p Q (hp.mono hKU) (hQ.mono hKU)
    (fun x hx => hQlt x (hKU hx)) A u
    (fun i j => (hA i j).mono hKU) (fun i => (hu i).mono hKU)
  have hballK : ball z (r / 2) ⊆ K := ball_subset_closedBall
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableOn.differentiableAt (s := ball z (r / 2))
    _ (ball_mem_nhds _ (by positivity))
  refine Complex.differentiableOn_tsum_of_summable_norm hb ?_ isOpen_ball ?_
  · intro q
    by_cases hq : reduceCharge D q = a
    · simp only [hq, if_true]
      apply DifferentiableOn.mono _ (hballK.trans hKU)
      exact (hp.mul (hQ.pow _)).mul
        (affine_coefficient_differentiableOn hA (fun i => (hu i).const_mul _) _)
    · simp [hq]
  · intro q x hx
    have bound := hmajor q x (hballK hx)
    by_cases hq : reduceCharge D q = a
    · simpa only [hq, if_true] using bound
    · simpa only [hq, if_false, norm_zero] using (norm_nonneg _).trans bound

#print axioms charge_sector_differentiableOn

open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open D5.S3.Analytic.OriginalSlitNome
open D5.S3.Analytic.OriginalHalfBinomialNome (Q0)
open OriginalFourMSlitMean OriginalGaussianExternalBlocks OriginalGaussianDeterminant
open OriginalFourMSignedOverlap (taggedMode)
open OriginalGaussianSourceMeans (sourceConstant)
open LatticeHalfFockChargedTensorCoefficients (chargeScalar chargeNorm)
open private isOpen_slitDomain ball_subset_slitDomain from
  D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open private chargeScalar_pair from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
open private nome_square_source from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal

private def leg {X : Type*} : X ⊕ X → Bool := Sum.elim (fun _ => false) (fun _ => true)

private def slitMatrix (D : LatticeData) {X : Type*} (e : X → External D) (r : ℂ)
    (i j : X ⊕ X) : ℂ :=
  let label := Sum.elim e e
  slitCovarianceEntry D (leg i) (leg j) (label i) (label j) r

private def slitLinear (D : LatticeData) {X : Type*} (e : X → External D) (r : ℂ)
    (i : X ⊕ X) : ℂ :=
  let x := Sum.elim e e i
  slitMeanEntry (leg i) x.1 x.2.2 r

/-- Each literal fixed-occupation charge term continued from the native sewing cusp. -/
def slitChargeTerm (D : LatticeData) (betaL gammaL betaR gammaR : Exponent D)
    (q : Charge D) (r : ℂ) : ℂ :=
  let F := fourSupport D betaL gammaL betaR gammaR
  let e := compactExternal D F
  rank24Determinant r * slitNome r ^ (chargeEnergy D q).toNat *
    affineCoefficient (slitMatrix D e r)
      (fun i => (bilinear D (unitCharge D (Sum.elim e e i).2.1) q : ℂ) * slitLinear D e r i)
      (externalOccupation D F betaL gammaL betaR gammaR)

/-- The continued charge-sector sum in the positive square coordinate. -/
def slitChargeSector (D : LatticeData) (a : ModTwoCharge D)
    (betaL gammaL betaR gammaR : Exponent D) (r : ℂ) : ℂ :=
  ∑' q : Charge D, if reduceCharge D q = a then slitChargeTerm D betaL gammaL betaR gammaR q r
    else 0

@[fun_prop]
theorem slitChargeSector_differentiableOn (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : ModTwoCharge D)
    (betaL gammaL betaR gammaR : Exponent D) :
    DifferentiableOn ℂ (slitChargeSector D a betaL gammaL betaR gammaR) slitDomain := by
  unfold slitChargeSector slitChargeTerm
  exact charge_sector_differentiableOn D hD betaL gammaL betaR gammaR a _ isOpen_slitDomain
    rank24Determinant slitNome rank24Determinant_analyticOnNhd.differentiableOn
    slitNome_analyticOnNhd.differentiableOn (fun _ => slitNome_norm_lt_one)
    (slitMatrix D _) (slitLinear D _)
    (fun i j => (slitCovarianceEntry_analyticOnNhd D _ _ _ _).differentiableOn)
    (fun i => (slitMeanEntry_analyticOnNhd _ _ _).differentiableOn)

private theorem rank24Determinant_eq_native (D : LatticeData) (h24 : D.rank = 24)
    {w : ℂ} (hw : ‖w‖ < 1) :
    rank24Determinant (w ^ 2) =
      Complex.exp (-(D.rank : ℂ) / 2 * gaussianLogDet w) := by
  have hmem := ball_subset_slitDomain (show w ^ 2 ∈ ball (0 : ℂ) 1 by
    rw [mem_ball_zero_iff, norm_pow]; exact pow_lt_one₀ (norm_nonneg w) hw (by decide))
  have hn : 1 - w ^ 2 ≠ 0 := Complex.slitPlane_ne_zero hmem
  have hw2 : ‖w ^ 2‖ < 1 := mem_ball_zero_iff.mp
    (show w ^ 2 ∈ ball (0 : ℂ) 1 by
      rw [mem_ball_zero_iff, norm_pow]; exact pow_lt_one₀ (norm_nonneg w) hw (by decide))
  have hpow : Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - w ^ 2)) ^ 12 =
      (1 - w ^ 2) ^ 3 := by
    rw [← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (12 : ℂ) * ((1 / 4 : ℂ) * Complex.log (1 - w ^ 2)) =
      (3 : ℂ) * Complex.log (1 - w ^ 2) by ring]
    exact (Complex.exp_nat_mul _ 3).trans (by rw [Complex.exp_log hn])
  have hexp : Complex.exp ((12 : ℂ) * gaussianLogDet w) = gaussianDet w ^ 12 := by
    simpa only [gaussianDet, Nat.cast_ofNat] using Complex.exp_nat_mul (gaussianLogDet w) 12
  rw [h24]
  norm_num only [Nat.cast_ofNat]
  rw [neg_mul, Complex.exp_neg, hexp,
    OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity hw,
    mul_pow, hpow, rank24Determinant, slitPeriod_eq_period hw2, mul_inv_rev, mul_comm]

/-- Agreement holds for every individual charge, throughout the native opening disk. -/
theorem slitChargeTerm_eq_native (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (betaL gammaL betaR gammaR : Exponent D) (q : Charge D) {w : ℂ} (hw : ‖w‖ < 1) :
    slitChargeTerm D betaL gammaL betaR gammaR q (w ^ 2) =
      sewnChargeTerm D betaL gammaL betaR gammaR q w := by
  let F := fourSupport D betaL gammaL betaR gammaR
  let e := compactExternal D F
  have hmatrix : slitMatrix D e (w ^ 2) = explicitEffectiveKernel D e w := by
    ext i j
    cases i <;> cases j
    · simpa [slitMatrix, leg, taggedMode] using slitCovarianceEntry_eq_native D e false false _ _ hw
    · simpa [slitMatrix, leg, taggedMode] using slitCovarianceEntry_eq_native D e false true _ _ hw
    · simpa [slitMatrix, leg, taggedMode] using slitCovarianceEntry_eq_native D e true false _ _ hw
    · simpa [slitMatrix, leg, taggedMode] using slitCovarianceEntry_eq_native D e true true _ _ hw
  have hlinear : (fun i => (bilinear D (unitCharge D (Sum.elim e e i).2.1) q : ℂ) *
      slitLinear D e (w ^ 2) i) = explicitMean D q e w := by
    funext i
    cases i
    · simpa [slitLinear, leg, taggedMode] using slitMeanEntry_eq_native D q e false _ hw
    · simpa [slitLinear, leg, taggedMode] using slitMeanEntry_eq_native D q e true _ hw
  let m := (chargeEnergy D q).toNat
  have hm : (m : ℤ) = chargeEnergy D q := Int.toNat_of_nonneg (chargeEnergy_nonneg D hD q)
  have hn : (chargeNorm D q : ℂ) = 2 * (m : ℂ) := by
    have h : (chargeNorm D q : ℤ) = 2 * (m : ℤ) := by
      rw [hm, two_chargeEnergy]
      rfl
    exact_mod_cast h
  have hs : (16 : ℂ) ^ (-chargeEnergy D q) = ((16 : ℂ) ^ m)⁻¹ := by
    rw [← hm, zpow_neg, zpow_natCast]
  have hw2 : w ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    exact pow_lt_one₀ (norm_nonneg w) hw (by decide)
  change rank24Determinant (w ^ 2) * slitNome (w ^ 2) ^ m *
      affineCoefficient (slitMatrix D e (w ^ 2)) _ _ =
    (chargeScalar D q * chargeScalar D (-q)) * w ^ (2 * m) * sewn D q e _ w
  rw [hmatrix, hlinear, rank24Determinant_eq_native D h24 hw,
    slitNome_eq_Q0 hw2, nome_square_source (mem_ball_zero_iff.mpr hw),
    chargeScalar_pair, hs, sewn, hn, div_pow, mul_pow, ← pow_mul, ← Complex.exp_nat_mul]
  rw [show (m : ℂ) * (2 * sourceConstant w) = 2 * (m : ℂ) * sourceConstant w by ring]
  ring

#print axioms slitChargeSector_differentiableOn
#print axioms slitChargeTerm_eq_native

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSectorContinuation
