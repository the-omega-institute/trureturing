import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipTaylor
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipNome
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation

/-! Actual fixed-occupation charge-sector sums through the D boundary. -/

open Complex Filter Set Metric
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSectorContinuation

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open OriginalFourMChargeNormal OriginalChargedRowSource OriginalGaussianSourceRestriction
open OriginalFourMEnergyCoefficient OriginalGaussianSewnAnalytic OriginalGaussianExternalBlocks
open OriginalFourMPeriodSource (dLip dPeriod dPeriod_eq_slit)
open OriginalFourMDLipMean OriginalFourMDLipNome
open D5.S3.Analytic.OriginalSlitNome
open private dPeriod_analyticAt dPeriod_ne_zero dLip_im_ne_zero mem_doubleSlit_of_im from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
open private leg slitMatrix slitLinear from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation

private def dDeterminant (upperA : Bool) (r : ℂ) : ℂ :=
  ((1 - r) ^ (3 : ℕ))⁻¹ * (dPeriod upperA r ^ (12 : ℕ))⁻¹

private theorem dDeterminant_analyticAt (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dDeterminant upperA) (t : ℂ) := by
  have ht₀ : (1 : ℂ) - (t : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht.ne)
  exact (((analyticAt_const.sub analyticAt_id).pow 3).inv (pow_ne_zero 3 ht₀)).mul
    (((dPeriod_analyticAt upperA ht).pow 12).inv (pow_ne_zero 12 (dPeriod_ne_zero upperA ht)))

private def dMatrix (D : LatticeData) (upperA : Bool) {X : Type*}
    (e : X → External D) (r : ℂ) (i j : X ⊕ X) : ℂ :=
  let label := Sum.elim e e
  dLipCovarianceEntry D upperA (leg i) (leg j) (label i) (label j) r

private def dLinear (D : LatticeData) (upperA : Bool) {X : Type*}
    (e : X → External D) (r : ℂ) (i : X ⊕ X) : ℂ :=
  let x := Sum.elim e e i
  dLipMeanEntry upperA (leg i) x.1 x.2.2 r

def dLipChargeSector (D : LatticeData) (upperA : Bool) (a : ModTwoCharge D)
    (betaL gammaL betaR gammaR : Exponent D) (r : ℂ) : ℂ :=
  let F := fourSupport D betaL gammaL betaR gammaR
  let e := compactExternal D F
  ∑' q : Charge D, if reduceCharge D q = a then
    dDeterminant upperA r * dNome upperA r ^ (chargeEnergy D q).toNat *
      affineCoefficient (dMatrix D upperA e r)
        (fun i => (bilinear D (unitCharge D (Sum.elim e e i).2.1) q : ℂ) * dLinear D upperA e r i)
        (externalOccupation D F betaL gammaL betaR gammaR)
    else 0

/-- The actual coset sum extends analytically through every positive point of
the D boundary on the indicated side. -/
theorem dLipChargeSector_analyticAt (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (upperA : Bool) (a : ModTwoCharge D)
    (betaL gammaL betaR gammaR : Exponent D) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipChargeSector D upperA a betaL gammaL betaR gammaR) (t : ℂ) := by
  let F := fourSupport D betaL gammaL betaR gammaR
  let e := compactExternal D F
  let T := CompactExternal D F ⊕ CompactExternal D F
  have hA : ∀ i j : T, AnalyticAt ℂ (fun r => dMatrix D upperA e r i j) (t : ℂ) :=
    fun i j => dLipCovarianceEntry_analyticAt D upperA _ _ _ _ ht
  have hu : ∀ i : T, AnalyticAt ℂ (fun r => dLinear D upperA e r i) (t : ℂ) :=
    fun i => dLipMeanEntry_analyticAt upperA _ _ _ ht
  have hAnear : ∀ᶠ r in 𝓝 (t : ℂ), ∀ i j : T,
      AnalyticAt ℂ (fun z => dMatrix D upperA e z i j) r :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => (hA i j).eventually_analyticAt
  have hunear : ∀ᶠ r in 𝓝 (t : ℂ), ∀ i : T,
      AnalyticAt ℂ (fun z => dLinear D upperA e z i) r :=
    eventually_all.mpr fun i => (hu i).eventually_analyticAt
  have hnear : ∀ᶠ r in 𝓝 (t : ℂ),
      AnalyticAt ℂ (dDeterminant upperA) r ∧ AnalyticAt ℂ (dNome upperA) r ∧
        ‖dNome upperA r‖ < 1 ∧ (∀ i j : T, AnalyticAt ℂ (fun z => dMatrix D upperA e z i j) r) ∧
          (∀ i : T, AnalyticAt ℂ (fun z => dLinear D upperA e z i) r) :=
    (dDeterminant_analyticAt upperA ht).eventually_analyticAt.and
      ((dNome_analyticAt upperA ht).eventually_analyticAt.and
        ((dNome_subunit_near upperA ht).and (hAnear.and hunear)))
  obtain ⟨δ, hδ, hB⟩ := Metric.mem_nhds_iff.mp hnear
  have hd := charge_sector_differentiableOn D hD betaL gammaL betaR gammaR a
    (ball (t : ℂ) δ) isOpen_ball (dDeterminant upperA) (dNome upperA)
    (fun r hr => (hB hr).1.differentiableAt.differentiableWithinAt)
    (fun r hr => (hB hr).2.1.differentiableAt.differentiableWithinAt)
    (fun r hr => (hB hr).2.2.1) (dMatrix D upperA e) (dLinear D upperA e)
    (fun i j r hr => ((hB hr).2.2.2.1 i j).differentiableAt.differentiableWithinAt)
    (fun i r hr => ((hB hr).2.2.2.2 i).differentiableAt.differentiableWithinAt)
  exact (hd.analyticOnNhd isOpen_ball) _ (mem_ball_self hδ)

theorem dLipChargeSector_eq_slit (D : LatticeData) (upperA : Bool) (a : ModTwoCharge D)
    (betaL gammaL betaR gammaR : Exponent D) {r : ℂ} (hr : r ∈ dLip upperA) :
    dLipChargeSector D upperA a betaL gammaL betaR gammaR r =
      slitChargeSector D a betaL gammaL betaR gammaR r := by
  have hri := dLip_im_ne_zero hr
  have hNome : dNome upperA r = slitNome r := by
    rw [dNome_eq_exp hr, slitNome_eq_exp]
    exact mem_doubleSlit_of_im hri
  unfold dLipChargeSector slitChargeSector slitChargeTerm
  apply tsum_congr
  intro q
  simp only [dDeterminant, rank24Determinant, dPeriod_eq_slit hr, hNome]
  have hA : ∀ i j, dMatrix D upperA (compactExternal D (fourSupport D betaL gammaL betaR gammaR))
        r i j = slitMatrix D (compactExternal D (fourSupport D betaL gammaL betaR gammaR)) r i j :=
    fun _ _ => dLipCovarianceEntry_eq_slit D upperA _ _ _ _ hr
  have hu : ∀ i, dLinear D upperA (compactExternal D (fourSupport D betaL gammaL betaR gammaR))
        r i = slitLinear D (compactExternal D (fourSupport D betaL gammaL betaR gammaR)) r i :=
    fun _ => dLipMeanEntry_eq_slit upperA _ _ _ hr
  rw [funext (fun i => funext (hA i))]
  simp only [hu]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSectorContinuation
