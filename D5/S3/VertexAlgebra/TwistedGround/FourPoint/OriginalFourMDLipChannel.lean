/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Analyticity, open-lip agreement and conditional A/D overlap of the original D channel. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipCovariance
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipNome
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms

/-! Analytic continuation of the original D channel and its overlap with the A chart. -/

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
open OriginalFourMPeriodSource (dLip dLip_mem_doubleSlit dPeriod dPeriod_analyticAt
  dPeriod_eq_slit dPeriod_ne_zero)
open OriginalFourMSignedOverlap (legSign)
open OriginalFourMSlitMean (analytic_coefficient_slice coefficient_congr slitMeanEntry
  slitCovarianceEntry)
open OriginalFourMDLipMean (dLipMean dLipMean_joint_analytic dLipMean_eventuallyEq
  dLipCovariance dLipCovariance_joint_analytic dLipCovariance_eq_of_means)
open OriginalFourMDLipNome (dNome dNome_analyticAt dNome_subunit_near dNome_eq_exp)
open D5.S3.Analytic.OriginalSlitNome (slitNome slitNome_eq_exp rank24Determinant)

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

private theorem dLipMeanEntry_eq_slit (upperA l e : Bool) (p : ℕ) {r : ℂ}
    (hr : r ∈ dLip upperA) :
    dLipMeanEntry upperA l e p r = slitMeanEntry l e p r := by
  unfold dLipMeanEntry slitMeanEntry
  apply coefficient_congr
  filter_upwards [dLipMean_eventuallyEq upperA e hr] with u hu
  rw [hu, dPeriod_eq_slit hr]

private theorem dLipCovarianceEntry_eq_slit (D : LatticeData) (upperA l k : Bool)
    (x y : External D) {r : ℂ} (hr : r ∈ dLip upperA) :
    dLipCovarianceEntry D upperA l k x y r = slitCovarianceEntry D l k x y r := by
  unfold dLipCovarianceEntry slitCovarianceEntry
  apply coefficient_congr
  filter_upwards [dLipMean_eventuallyEq upperA y.1 hr] with v hv
  apply coefficient_congr
  filter_upwards [dLipMean_eventuallyEq upperA x.1 hr] with u hu
  rw [dLipCovariance_eq_of_means upperA l k x.1 y.1 hr hu hv]

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

/-- The D-lip and canonical slit sector sums agree at each point on the open lip. -/
theorem dLipChargeSector_eq_slit (D : LatticeData) (upperA : Bool) (a : ModTwoCharge D)
    (betaL gammaL betaR gammaR : Exponent D) {r : ℂ} (hr : r ∈ dLip upperA) :
    dLipChargeSector D upperA a betaL gammaL betaR gammaR r =
      slitChargeSector D a betaL gammaL betaR gammaR r := by
  have hNome := (dNome_eq_exp hr).trans (slitNome_eq_exp (dLip_mem_doubleSlit hr)).symm
  let e := compactExternal D (fourSupport D betaL gammaL betaR gammaR)
  have hMatrix : dMatrix D upperA e r = slitMatrix D e r := by
    funext i j
    cases i <;> cases j <;> exact dLipCovarianceEntry_eq_slit D upperA _ _ _ _ hr
  have hLinear : dLinear D upperA e r = slitLinear D e r := by
    funext i
    cases i <;> exact dLipMeanEntry_eq_slit upperA _ _ _ hr
  dsimp only [e] at hMatrix hLinear
  unfold dLipChargeSector slitChargeSector slitChargeTerm
  apply tsum_congr
  intro q
  simp only [dDeterminant, rank24Determinant, dPeriod_eq_slit hr, hNome, hMatrix, hLinear]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSectorContinuation

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open FourPoint.FourPointChannelCoefficients (laurent loweredLaurent loweringCutoff)
open FourPoint.OriginalFourMChargeNormal (projectOccupations)
open OriginalFourMSectorContinuation (dLipChargeSector dLipChargeSector_analyticAt
  dLipChargeSector_eq_slit)
open OriginalFourMPeriodSource (dLip dLip_mem_doubleSlit eq_near_dLip_of_real_germ)
open OriginalFourPointChartGluing (Ω U_A U_D)
open FourPoint.OriginalFourMActualChart (parameter)

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

private theorem dLipNumerator_eq_slitDiagonal (D : LatticeData) (upperA : Bool)
    (H K : ℕ) (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D)
    {t : ℂ} (ht : t ∈ dLip upperA) :
    dLipNumerator D upperA H K s P Q R S a t = slitDiagonal D H K s P Q R S a t := by
  unfold dLipNumerator slitDiagonal
  simp only [dLipChargeSector_eq_slit D upperA a _ _ _ _ ht]

/-- On the open D lip the lowered D continuation is the canonical slit D channel. -/
theorem dLipChannel_eq_slit (D : LatticeData) (upperA : Bool)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (b : ModTwoCharge D)
    {t : ℂ} (ht : t ∈ dLip upperA) :
    dLipChannel D upperA H K L m n r P Q R S b t = slitChannelD D H K L m n r P Q R S b t := by
  simp only [dLipChannel, slitChannelD, slitLowered, loweredLaurent, laurent, neg_neg,
    dLipNumerator_eq_slitDiagonal D upperA _ _ _ _ _ _ _ _ ht]

/-- Real-neighborhood agreement with the actual D continuation gives an
interior A/D overlap in the physical chart coordinate. -/
theorem slit_AD_overlap (D : LatticeData) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (upperA : Bool) (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (b : ModTwoCharge D)
    {t : ℝ} (ht : 1 < t)
    (hReal : ∀ᶠ s : ℝ in 𝓝 t, slitChannelA D H K (m + n + r) P Q R S b (1 - (s : ℂ)) =
      dLipChannel D upperA H K L m n r P Q R S b (s : ℂ)) :
    ∃ y ∈ U_A ∩ U_D, ∀ᶠ z in 𝓝 y,
      slitChannelA D H K (m + n + r) P Q R S b (parameter .A z) =
        slitChannelD D H K L m n r P Q R S b (parameter .D z) := by
  have hmem : 1 - (t : ℂ) ∈ Ω := by
    refine ⟨?_, sub_ne_zero.mpr (by exact_mod_cast ht.ne)⟩
    change 1 - (1 - (t : ℂ)) ∈ Complex.slitPlane
    rw [sub_sub_cancel]
    exact Complex.ofReal_mem_slitPlane.mpr (zero_lt_one.trans ht)
  have hA := (slitChannelA_analyticOnNhd D hD H K (m + n + r) P Q R S b _ hmem).comp
    (f := fun u : ℂ => 1 - u) (analyticAt_const.sub analyticAt_id)
  obtain ⟨u, hu, he⟩ := eq_near_dLip_of_real_germ upperA hA
    (dLipChannel_analyticAt D hD upperA H K L m n r P Q R S b ht) hReal
    (eventuallyEq_nhdsWithin_of_eqOn fun _ hz =>
      dLipChannel_eq_slit D upperA H K L m n r P Q R S b hz)
  have hSlit := dLip_mem_doubleSlit hu
  have hu₀ : u ≠ 0 := Complex.slitPlane_ne_zero hSlit.2
  have hu₁ : 1 - u ≠ 0 := Complex.slitPlane_ne_zero hSlit.1
  have hyA : u⁻¹ ∈ U_A := by
    change u⁻¹ ≠ 0 ∧ 1 - (u⁻¹)⁻¹ ∈ Ω
    rw [inv_inv]
    refine ⟨inv_ne_zero hu₀, ?_, hu₁⟩
    change 1 - (1 - u) ∈ Complex.slitPlane
    simpa only [sub_sub_cancel] using hSlit.2
  have hyD : u⁻¹ ∈ U_D := by
    change u⁻¹ ≠ 0 ∧ (u⁻¹)⁻¹ ∈ Ω
    rw [inv_inv]
    exact ⟨inv_ne_zero hu₀, hSlit.1, hu₀⟩
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (𝓝 (u⁻¹)) (𝓝 u) := by
    simpa only [inv_inv] using (continuousAt_inv₀ (inv_ne_zero hu₀)).tendsto
  exact ⟨u⁻¹, ⟨hyA, hyD⟩, hinv.eventually he⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
