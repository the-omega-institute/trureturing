/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Analyticity of the original lowered D-lip Laurent channel at real boundary points. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipCovariance
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipNome
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation

/-! Analyticity of the original charge-sector sums and lowered Laurent channel on either D lip. -/

open Filter Set Metric
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSectorContinuation

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open FourPoint.OriginalFourMChargeNormal
open OriginalChargedRowSource OriginalGaussianSourceRestriction
open OriginalFourMEnergyCoefficient OriginalGaussianSewnAnalytic OriginalGaussianExternalBlocks
open OriginalCurrentMetric
open OriginalFourMPeriodSource (dPeriod dPeriod_analyticAt dPeriod_ne_zero)
open OriginalFourMSignedOverlap (legSign)
open OriginalFourMSlitMean (analytic_coefficient_slice)
open OriginalFourMDLipMean (dLipMean dLipMean_joint_analytic dLipCovariance
  dLipCovariance_joint_analytic)
open OriginalFourMDLipNome (dNome dNome_analyticAt dNome_subunit_near)

private def dLipMeanEntry (upperA l e : Bool) (p : ℕ) (r : ℂ) : ℂ :=
  coefficient p (fun u => -legSign l * dLipMean upperA e u r / dPeriod upperA r)

private theorem dLipMeanEntry_analyticAt (upperA l e : Bool) (p : ℕ) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipMeanEntry upperA l e p) (t : ℂ) := by
  have hf : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      -legSign l * dLipMean upperA e z.1 z.2 / dPeriod upperA z.2) (0, (t : ℂ)) :=
    (analyticAt_const.mul (dLipMean_joint_analytic upperA e ht)).div
      ((dPeriod_analyticAt upperA ht).comp_of_eq
        (f := fun z : ℂ × ℂ => z.2) analyticAt_snd rfl) (dPeriod_ne_zero upperA ht)
  exact analytic_coefficient_slice hf p

private def dLipCovarianceEntry (D : LatticeData) (upperA l k : Bool)
    (x y : External D) (r : ℂ) : ℂ :=
  coefficient y.2.2 (fun v => coefficient x.2.2 (fun u =>
    gramComplex D x.2.1 y.2.1 * dLipCovariance upperA l k x.1 y.1 u v r))

private theorem dLipCovarianceEntry_analyticAt (D : LatticeData) (upperA l k : Bool)
    (x y : External D) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipCovarianceEntry D upperA l k x y) (t : ℂ) := by
  have hf : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ =>
      gramComplex D x.2.1 y.2.1 * dLipCovariance upperA l k x.1 y.1 p.1 p.2.1 p.2.2)
      (0, 0, (t : ℂ)) :=
    analyticAt_const.mul (dLipCovariance_joint_analytic upperA l k x.1 y.1 ht)
  exact analytic_coefficient_slice (analytic_coefficient_slice hf x.2.2) y.2.2

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
  dLipCovarianceEntry D upperA i.isRight j.isRight (label i) (label j) r

private def dLinear (D : LatticeData) (upperA : Bool) {X : Type*}
    (e : X → External D) (r : ℂ) (i : X ⊕ X) : ℂ :=
  let x := Sum.elim e e i
  dLipMeanEntry upperA i.isRight x.1 x.2.2 r

/-- The D-lip coset charge sum at four fixed occupations. -/
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

/-- The fixed-occupation coset sum is analytic at each real point greater than one
for the selected D lip. -/
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

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSectorContinuation

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open FourPoint.FourPointChannelCoefficients (laurent loweredLaurent loweringCutoff)
open FourPoint.OriginalFourMChargeNormal (projectOccupations)
open OriginalFourMSectorContinuation (dLipChargeSector dLipChargeSector_analyticAt)

private def dLipNumerator (D : LatticeData) (upperA : Bool) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (t : ℂ) : ℂ :=
  projectOccupations D H K 0 (s - H - K + 1) P Q R S
    (fun betaL gammaL betaR gammaR =>
      dLipChargeSector D upperA a betaL gammaL betaR gammaR t)

private theorem dLipNumerator_analyticAt (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (upperA : Bool)
    (H K : ℕ) (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipNumerator D upperA H K s P Q R S a) (t : ℂ) := by
  have hSector (b c e f : Exponent D) :
      AnalyticAt ℂ (dLipChargeSector D upperA a b c e f) (t : ℂ) :=
    dLipChargeSector_analyticAt D hD upperA a b c e f ht
  unfold dLipNumerator projectOccupations
  fun_prop

/-- The signed D-lip Laurent channel with the native finite lowering detector. -/
def dLipChannel (D : LatticeData) (upperA : Bool) (H K L : ℕ) (m n r : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) (t : ℂ) : ℂ :=
  ∑ a, quadraticSign D (a + b) *
    loweredLaurent ((H : ℤ) + L) (m + n + r) (loweringCutoff H K L m n r)
      (fun ell u => dLipNumerator D upperA H L (m + n + r + (ell : ℤ))
        P R Q ((oscillatorLower D ^ ell) S) a (-u)) t

/-- For either lip, the lowered D channel is analytic at every real t > 1. -/
theorem dLipChannel_analyticAt (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (upperA : Bool)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (b : ModTwoCharge D) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipChannel D upperA H K L m n r P Q R S b) (t : ℂ) := by
  have ht₀ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hPow : AnalyticAt ℂ (fun z : ℂ => (-z) ^ (-((H : ℤ) + L))) (t : ℂ) :=
    analyticAt_id.neg.zpow (neg_ne_zero.mpr ht₀)
  unfold dLipChannel
  simp only [loweredLaurent, laurent, neg_neg]
  apply Finset.analyticAt_fun_sum
  intro a _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro ell _
  exact analyticAt_const.mul (hPow.mul (dLipNumerator_analyticAt D hD upperA H L
    (m + n + r + (ell : ℤ)) P R Q ((oscillatorLower D ^ ell) S) a ht))

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
